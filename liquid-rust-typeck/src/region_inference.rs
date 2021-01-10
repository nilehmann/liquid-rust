use std::collections::{HashMap, HashSet};

use crate::{
    env::{ContEnv, Env},
    synth::Synth,
};
use ast::{Place, StatementKind};
use liquid_rust_core::{
    ast::{
        self,
        visitor::{self as vis, Visitor},
        FnBody, Statement,
    },
    ty::{self, TyCtxt, TyS},
};

pub struct RegionInferer<'a> {
    conts: ContEnv<'a>,
    tcx: &'a TyCtxt,
    env: Env<'a>,
    constraints: Constraints,
}

impl<'a> RegionInferer<'a> {
    pub fn new(tcx: &'a TyCtxt) -> Self {
        RegionInferer {
            conts: ContEnv::new(tcx),
            tcx,
            env: Env::new(tcx),
            constraints: Constraints::new(),
        }
    }

    pub fn infer<I>(
        mut self,
        func: &ast::FnDef<I>,
        fn_ty: &ty::FnTy,
    ) -> HashMap<ty::RegionVid, Vec<Place>> {
        self.env.insert_locals(fn_ty.locals(&func.params));
        self.env.extend_heap(&fn_ty.in_heap);
        self.conts
            .define_ret_cont(func.ret, &func.ty, self.env.vars_in_scope());
        self.visit_fn_body(&func.body);
        self.constraints.solve()
    }
}

impl<I> Visitor<I> for RegionInferer<'_> {
    fn visit_fn_body(&mut self, body: &FnBody<I>) {
        match body {
            FnBody::Jump { target, args } => {
                let cont_ty = &self.conts[target];
                for (x, l) in cont_ty.locals(args) {
                    let ty1 = self.env.lookup(&Place::from(x));
                    let ty2 = &cont_ty.heap[&l];
                    subtyping(
                        &mut self.constraints,
                        self.env.heap(),
                        ty1,
                        &cont_ty.heap,
                        ty2,
                    );
                }
            }
            FnBody::Ite { then, else_, .. } => {
                let snapshot = self.env.snapshot();
                self.visit_fn_body(then);
                self.env.rollback_to(snapshot);
                self.visit_fn_body(else_);
            }
            FnBody::LetCont(defs, rest) => {
                for def in defs {
                    self.conts
                        .define_cont(def.name, &def.ty, self.env.vars_in_scope());
                }
                for def in defs {
                    let cont_ty = &self.conts[&def.name];
                    let snapshot = self.env.snapshot_without_locals();
                    let locals = cont_ty.locals(&def.params);
                    self.env.insert_locals(locals);
                    self.env.extend_heap(&cont_ty.heap);
                    self.visit_cont_def(def);
                    self.env.rollback_to(snapshot);
                }
                self.visit_fn_body(rest);
            }
            _ => vis::walk_fn_body(self, body),
        }
    }

    fn visit_stmnt(&mut self, stmnt: &Statement<I>) {
        match &stmnt.kind {
            StatementKind::Let(local, layout) => {
                let ty = self.tcx.mk_ty_for_layout(layout);
                self.env.alloc(*local, ty);
            }
            StatementKind::Assign(place, rvalue) => {
                let ty = rvalue.synth(self.tcx, &mut self.env);
                self.env.update(place, ty);
            }
            StatementKind::Drop(local) => {
                self.env.drop(local);
            }
        }
    }
}

fn subtyping(
    constraints: &mut Constraints,
    heap1: &ty::Heap,
    ty1: &TyS,
    heap2: &ty::Heap,
    ty2: &TyS,
) {
    match (ty1.kind(), ty2.kind()) {
        (ty::TyKind::Fn(..), ty::TyKind::Fn(..)) => todo!(),
        (ty::TyKind::Tuple(tup1), ty::TyKind::Tuple(tup2)) if tup1.len() == tup2.len() => {
            for (ty1, ty2) in tup1.types().zip(tup2.types()) {
                subtyping(constraints, heap1, ty1, heap2, ty2);
            }
        }
        (ty::TyKind::Ref(bk1, r1, l1), ty::TyKind::Ref(bk2, r2, l2)) if bk1 >= bk2 => {
            constraints.add(r1.clone(), r2.clone());
            subtyping(constraints, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (ty::TyKind::OwnRef(l1), ty::TyKind::OwnRef(l2)) => {
            subtyping(constraints, heap1, &heap1[l1], heap2, &heap2[l2]);
        }
        (ty::TyKind::Refine(bty1, ..), ty::TyKind::Refine(bty2, ..)) if bty1 == bty2 => {}
        (_, ty::TyKind::Uninit(n)) if ty1.size() == *n => {}
        _ => bug!("{} {}", ty1, ty2),
    }
}

struct Constraints(Vec<(ty::Region, ty::Region)>);

impl Constraints {
    fn new() -> Self {
        Constraints(Vec::new())
    }

    fn add(&mut self, r1: ty::Region, r2: ty::Region) {
        self.0.push((r1, r2))
    }

    fn solve(self) -> HashMap<ty::RegionVid, Vec<Place>> {
        let mut map: HashMap<_, HashSet<_>> = HashMap::new();
        for (r1, r2) in self.0 {
            match (r1, r2) {
                (ty::Region::Concrete(places), ty::Region::Infer(id)) => {
                    map.entry(id).or_default().extend(places)
                }
                (ty::Region::Infer(..), _) => bug!(),
                _ => {}
            }
        }
        map.into_iter()
            .map(|(id, places)| (id, places.into_iter().collect()))
            .collect()
    }
}
