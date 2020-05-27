extern crate rustc_mir;

use super::{Binder, Operand, Place, Pred, ReftType, Scalar, Var};
use crate::context::LiquidRustCtxt;
use crate::smtlib2::{SmtRes, Solver};
use crate::syntax::ast::{BinOpKind, UnOpKind};
use rustc_data_structures::graph::{vec_graph::VecGraph, WithStartNode};
use rustc_hir::BodyId;
use rustc_index::vec::IndexVec;
use rustc_index::vec::Idx;
use rustc_middle::mir::{self, Constant, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{self, Ty};
use std::collections::{HashMap, HashSet};

pub fn check_body(cx: &LiquidRustCtxt<'_, '_>, body_id: BodyId) {
    ReftChecker::new(cx, body_id).check_body();
}

struct DominatorTree<'lr, 'tcx> {
    /// The dominator tree, generated from the control-flow graph of the
    /// bbs in the function
    dom_tree: VecGraph<mir::BasicBlock>,

    /// The new predicates which we know for sure to be true before entering
    /// a basic block
    known_preds: HashMap<mir::BasicBlock, &'lr Pred<'lr, 'tcx>>,
}

struct ReftChecker<'a, 'lr, 'tcx> {
    cx: &'a LiquidRustCtxt<'lr, 'tcx>,
    mir: &'a mir::Body<'tcx>,
    reft_types: HashMap<mir::Local, Binder<&'lr ReftType<'lr, 'tcx>>>,
}

impl<'a, 'lr, 'tcx> ReftChecker<'a, 'lr, 'tcx> {
    pub fn new(cx: &'a LiquidRustCtxt<'lr, 'tcx>, body_id: BodyId) -> Self {
        let reft_types = cx.local_decls(body_id).clone();
        let mir = cx.optimized_mir(body_id);
        ReftChecker {
            cx,
            mir,
            reft_types,
        }
    }

    /// Transforms the control flow graph into a dominator tree, which is used
    /// so that we can later do a depth-first traversal in dominator-tree-order
    /// when type-checking the body of this function.
    ///
    /// The dominator tree also contains edge information - predicates which
    /// we know to be true after we've travelled along an edge.
    pub fn build_dominator_tree(&mut self) -> DominatorTree<'lr, 'tcx> {
        let mut edges = Vec::new();
        let mut known_preds = HashMap::new();
        let dominators = self.mir.dominators();

        for (bb, bbd) in self.mir.basic_blocks().iter_enumerated() {
            let dr = dominators.immediate_dominator(bb);
            if dr != bb {
                edges.push((dr, bb));
            }

            if let Some(terminator) = &bbd.terminator {
                match &terminator.kind {
                    mir::TerminatorKind::SwitchInt {
                        discr,
                        values,
                        switch_ty,
                        targets,
                    } => {
                        let discr = self.cx.mk_operand(Operand::from_mir(discr));
                        for (value, target) in values.iter().zip(targets.iter()) {
                            let value = self.cx.mk_operand(Operand::from_bits(
                                self.cx.tcx(),
                                *value,
                                switch_ty,
                            ));
                            let cond = self.cx.mk_binary(discr, BinOpKind::Eq, value);
                            known_preds.insert(*target, cond);
                        }
                    }
                    mir::TerminatorKind::Assert {
                        cond,
                        expected,
                        target,
                        ..
                    } => {
                        let mut cond = self.cx.mk_operand(Operand::from_mir(cond));
                        if !expected {
                            cond = self.cx.mk_unary(UnOpKind::Not, cond);
                        }
                        known_preds.insert(*target, cond);
                    }
                    _ => {}
                }
            }
        }

        return DominatorTree {
            known_preds,
            dom_tree: VecGraph::new(self.mir.basic_blocks().len(), edges),
        };
    }

    pub fn check_body(&mut self) {
        let dom_tree = self.build_dominator_tree();

        // Typing context:
        // We iteratively build our typing context as we go.
        // env is the actual typing environment, while depths is the depth
        // at which each corresponding item in env was added.
        let mut env: Vec<&'lr Pred<'lr, 'tcx>> = Vec::new();
        let mut depths = Vec::new();

        // Before we do anything, we have to push the refinement predicates
        // for our return type and argument types
        // These locals are defined before any statements are executed, so
        // we have to manually plumb them into our typing context (they
        // are never assigned with check_assign)
        for (local, rt) in self.reft_types.iter() {
            if let Some(pred) = rt.pred() {
                env.push(self.cx.open_pred(pred, Operand::from_local(*local)));
            }
        }

        // Our queue is a Vec since we want a stack, not a deque
        // The first element of the tuple is the depth of the current node,
        // while the second is the actual basic block index itself
        let mut queue: Vec<(usize, mir::BasicBlock)> =
            Vec::with_capacity(self.mir.basic_blocks().len());
        queue.push((1, self.mir.start_node()));

        while let Some((depth, bb)) = queue.pop() {
            dbg!(&env);
            dbg!(&depths);
            
            print!("\nbb{}:", bb.index());
            let bbd = &self.mir[bb];

            // If our current depth is not greater than the depth of the top
            // item in the context, we pop until this is true.
            while let Some(d) = depths.pop() {
                if depth > d {
                    depths.push(d);
                    break;
                } else {
                    let _ = env.pop();
                }
            }

            // We then push our known pred, if it exists
            if let Some(p) = dom_tree.known_preds.get(&bb) {
                env.push(p);
                depths.push(depth);
            }

            for statement in bbd.statements.iter() {
                match &statement.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        println!("\n  {:?}", statement);
                        let ty = place.ty(self, self.cx.tcx()).ty;
                        let lhs = self.rvalue_reft_type(ty, rvalue);
                        println!("    {:?}", env);
                        self.check_assign(*place, &mut env, &mut depths, depth, lhs);
                    }
                    StatementKind::StorageLive(_)
                    | StatementKind::StorageDead(_)
                    | StatementKind::Nop => {}
                    _ => todo!("{:?}", statement),
                }
            }

            if let Some(terminator) = &bbd.terminator {
                println!("\n  {:?}", terminator.kind);
                match &terminator.kind {
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        ..
                    } => {
                        if let Some((place, _)) = destination {
                            let fun_type = self.operand_reft_type(func);
                            if place.projection.len() > 0 {
                                todo!();
                            }
                            let values: Vec<_> = args.iter().map(Operand::from_mir).collect();
                            let (formals, ret) = self.cx.split_fun_type(fun_type, &values);

                            println!("    {:?}", env);
                            for (arg, formal) in args.iter().zip(formals) {
                                let actual = self.operand_reft_type(arg);
                                self.check_subtyping(&env, actual, formal);
                            }
                            println!("");
                            self.check_assign(*place, &mut env, &mut depths, depth, ret);
                        } else {
                            todo!("implement checks for non converging calls")
                        }
                    }
                    TerminatorKind::Resume
                    | TerminatorKind::Goto { .. }
                    | TerminatorKind::SwitchInt { .. }
                    | TerminatorKind::Assert { .. }
                    | TerminatorKind::Abort
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable => {}
                    _ => todo!("{:?}", terminator.kind),
                };
            }

            // We push the bbs that this bb immediately dominates to the queue.
            for domd in dom_tree.dom_tree.successors(bb) {
                queue.push((depth + 1, *domd));
            }
        }
        println!("---------------------------");
    }

    fn check_assign(
        &mut self,
        place: mir::Place,
        env: &mut Vec<&'lr Pred<'lr, 'tcx>>,
        depths: &mut Vec<usize>,
        depth: usize,
        lhs: Binder<&'lr ReftType<'lr, 'tcx>>,
    ) {
        if place.projection.len() > 0 {
            todo!();
        }
        let local = place.local;
        if let Some(rhs) = self.reft_types.get(&local) {
            self.check_subtyping(&env, lhs, *rhs);
        } else if !self.mir.local_decls[local].is_user_variable() {
            println!("    infer {:?}:{:?}", local, lhs);
            self.reft_types.insert(local, lhs);
            if let Some(pred) = lhs.pred() {
                env.push(self.cx.open_pred(pred, Operand::from_local(local)));
                depths.push(depth);
            }
        }
    }

    fn check_subtyping(
        &self,
        env: &[&'lr Pred<'lr, 'tcx>],
        lhs: Binder<&'lr ReftType<'lr, 'tcx>>,
        rhs: Binder<&'lr ReftType<'lr, 'tcx>>,
    ) {
        let lhs = self.cx.open_with_fresh_vars(lhs);
        let rhs = self.cx.open_with_fresh_vars(rhs);
        match (lhs, rhs) {
            (ReftType::Fun { .. }, ReftType::Fun { .. }) => todo!(),
            (ReftType::Reft(_, lhs), ReftType::Reft(_, rhs)) => {
                let r = self.check(&env, lhs, rhs);
                if let Err(e) = r {
                    println!("    {:?}", e);
                }
            }
            _ => bug!("refinement types must have the same shape"),
        }
    }

    fn operand_reft_type(&self, operand: &mir::Operand<'tcx>) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let reft_ty = match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                let ty = place.ty(self, self.cx.tcx()).ty;
                match ty.kind {
                    ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                    ty::FnPtr(..) => todo!(),
                    _ => {
                        let place = Place {
                            var: Var::Local(place.local),
                            projection: place.projection,
                        };
                        let place = self.cx.mk_operand(Operand::Place(place));
                        self.cx
                            .mk_reft(ty, self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, place))
                    }
                }
            }
            mir::Operand::Constant(box Constant { literal, .. }) => match literal.ty.kind {
                ty::FnDef(def_id, _) => return self.cx.reft_type_for(def_id),
                ty::FnPtr(..) => todo!(),
                _ => {
                    let scalar = match Scalar::from_const(literal) {
                        Some(scalar) => scalar,
                        None => todo!("{:?}", literal),
                    };
                    let ty = literal.ty;
                    let constant = self.cx.mk_operand(Operand::Constant(literal.ty, scalar));
                    self.cx
                        .mk_reft(ty, self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, constant))
                }
            },
        };
        Binder::bind(reft_ty)
    }

    pub fn rvalue_reft_type(
        &self,
        ty: Ty<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Binder<&'lr ReftType<'lr, 'tcx>> {
        let reft_ty = match rvalue {
            Rvalue::Use(operand) => return self.operand_reft_type(operand),
            // v:{v.0 == lhs + rhs}
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let op = mir_binop_to_refine_op(*op);
                let lhs = self.cx.mk_operand(Operand::from_mir(lhs));
                let rhs = self.cx.mk_operand(Operand::from_mir(rhs));
                let bin = self.cx.mk_binary(lhs, op, rhs);
                let ty = ty.tuple_fields().next().unwrap();
                let bin = self.cx.mk_binary(
                    self.cx.mk_operand(Operand::Place(self.cx.mk_place_field(
                        Place::nu(),
                        mir::Field::new(0),
                        ty,
                    ))),
                    BinOpKind::Eq,
                    bin,
                );
                self.cx.mk_reft(ty, bin)
            }
            // v:{v == lhs + rhs}
            Rvalue::BinaryOp(op, lhs, rhs) => {
                let op = mir_binop_to_refine_op(*op);
                let lhs = self.cx.mk_operand(Operand::from_mir(lhs));
                let rhs = self.cx.mk_operand(Operand::from_mir(rhs));
                let bin = self.cx.mk_binary(lhs, op, rhs);
                let bin = self.cx.mk_binary(self.cx.nu, BinOpKind::Eq, bin);
                self.cx.mk_reft(ty, bin)
            }
            _ => todo!("{:?}", rvalue),
        };
        Binder::bind(reft_ty)
    }

    fn check(
        &self,
        env: &[&'lr Pred<'lr, 'tcx>],
        lhs: &'lr Pred<'lr, 'tcx>,
        rhs: &'lr Pred<'lr, 'tcx>,
    ) -> SmtRes<()> {
        let mut solver = Solver::default(())?;
        let mut places = HashSet::new();
        for pred in env.iter().chain(&[lhs, rhs]) {
            pred.iter_places(|place| {
                places.insert(place);
            })
        }

        for place in places {
            let sort = match &place.ty(self, self.cx.tcx()).kind {
                ty::Int(..) => "Int",
                ty::Bool => "Bool",
                ty @ _ => todo!("{:?}", ty),
            };
            solver.declare_const(&place, sort)?;
        }

        for pred in env {
            solver.assert(pred)?;
        }

        let not_rhs = Pred::Unary(UnOpKind::Not, rhs);
        solver.assert(lhs)?;
        solver.assert(&not_rhs)?;

        let b = solver.check_sat()?;
        println!("      {{{:?}}} <: {{{:?}}}  {}", lhs, rhs, !b);
        Ok(())
    }
}

impl<'tcx> mir::HasLocalDecls<'tcx> for ReftChecker<'_, '_, 'tcx> {
    fn local_decls(&self) -> &IndexVec<mir::Local, mir::LocalDecl<'tcx>> {
        &self.mir.local_decls
    }
}

pub fn mir_binop_to_refine_op(op: mir::BinOp) -> BinOpKind {
    match op {
        mir::BinOp::Add => BinOpKind::Add,
        mir::BinOp::Sub => BinOpKind::Sub,
        mir::BinOp::Mul => BinOpKind::Mul,
        mir::BinOp::Div => BinOpKind::Div,
        mir::BinOp::Eq => BinOpKind::Eq,
        mir::BinOp::Lt => BinOpKind::Lt,
        mir::BinOp::Ge => BinOpKind::Ge,
        mir::BinOp::Gt => BinOpKind::Gt,
        mir::BinOp::Le => BinOpKind::Le,
        mir::BinOp::Ne
        | mir::BinOp::Rem
        | mir::BinOp::BitXor
        | mir::BinOp::BitAnd
        | mir::BinOp::BitOr
        | mir::BinOp::Shl
        | mir::BinOp::Shr
        | mir::BinOp::Offset => todo!("{:?}", op),
    }
}

