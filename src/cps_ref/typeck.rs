use std::{collections::HashMap, fmt::Debug};

use super::{ast::*, context::LiquidRustCtxt};

type LocalsCtxt = HashMap<Local, OwnRef>;
type LocationsCtxt<'lr> = HashMap<Location, Ty<'lr>>;

struct TyCtxt<'lr> {
    frames: Vec<CtxtFrame<'lr>>,
    cx: &'lr LiquidRustCtxt<'lr>,
    curr_location: u32,
}

impl Debug for TyCtxt<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut locations: HashMap<&Location, _> = HashMap::new();
        let mut locals: HashMap<&Local, _> = HashMap::new();
        for frame in &self.frames {
            locations.extend(frame.locations.iter());
            locals.extend(frame.locals.iter());
        }
        write!(f, "{:?}; {:?}", locations, locals)
    }
}

#[derive(Default)]
struct CtxtFrame<'lr> {
    locations: LocationsCtxt<'lr>,
    locals: LocalsCtxt,
}

impl<'lr> TyCtxt<'lr> {
    pub fn new(
        cx: &'lr LiquidRustCtxt<'lr>,
        locations: LocationsCtxt<'lr>,
        locals: LocalsCtxt,
    ) -> Self {
        let frame = CtxtFrame { locations, locals };
        Self {
            frames: vec![frame],
            cx,
            curr_location: 0,
        }
    }

    pub fn from_fn_def(cx: &'lr LiquidRustCtxt<'lr>, fn_def: &FnDef<'lr>) -> Self {
        Self::new(
            cx,
            fn_def.heap.iter().copied().collect(),
            fn_def.args.iter().copied().collect(),
        )
    }

    pub fn push_frame(&mut self) {
        self.frames.push(CtxtFrame::default());
    }

    pub fn pop_frame(&mut self) {
        self.frames.pop().unwrap();
    }

    pub fn lookup(&self, place: &Place) -> (Pred<'lr>, Ty<'lr>) {
        let OwnRef(l) = self.lookup_local(place.local);
        let typ = self.lookup_location(l);
        let pred = self.cx.mk_place(l.into(), &place.projection);
        (pred, typ.project(&place.projection))
    }

    fn lookup_local(&self, local: Local) -> OwnRef {
        for frame in self.frames.iter().rev() {
            if let Some(ownref) = frame.locals.get(&local) {
                return *ownref;
            }
        }
        bug!("Cannot find local `{:?}`", local);
    }

    fn lookup_location(&self, location: Location) -> Ty<'lr> {
        for frame in self.frames.iter().rev() {
            if let Some(typ) = frame.locations.get(&location) {
                return typ;
            }
        }
        bug!("Cannot find location `{:?}`", location);
    }

    fn insert_location(&mut self, location: Location, typ: Ty<'lr>) {
        let frame = self.frames.last_mut().unwrap();
        frame.locations.insert(location, typ);
    }

    fn insert_local(&mut self, local: Local, ownref: OwnRef) {
        let frame = self.frames.last_mut().unwrap();
        frame.locals.insert(local, ownref);
    }

    pub fn uninit(&mut self, place: &Place) {
        let (_, t) = self.lookup(place);
        self.update(place, self.cx.mk_uninit(t.size()));
    }

    pub fn update(&mut self, place: &Place, typ: Ty<'lr>) {
        let OwnRef(l) = self.lookup_local(place.local);
        let updated = self
            .lookup_location(l)
            .update_at(self.cx, &place.projection, typ);
        let fresh = self.fresh_location();
        self.insert_location(fresh, updated);
        self.insert_local(place.local, OwnRef(fresh));
    }

    pub fn alloc(&mut self, x: Local, layout: &TypeLayout) {
        let l = self.fresh_location();
        self.insert_location(l, self.cx.mk_ty_for_layout(layout));
        self.insert_local(x, OwnRef(l));
    }

    fn fresh_location(&mut self) -> Location {
        let l = self.curr_location;
        self.curr_location += 1;
        Location(Symbol::intern(&format!("l{}", l)))
    }

    pub fn check_call(
        &mut self,
        in_heap: &Heap<'lr>,
        params: &[OwnRef],
        out_heap: &Heap<'lr>,
        out_ty: OwnRef,
        args: &[Local],
    ) -> Local {
        // Check against function arguments
        let locations_f = in_heap.iter().copied().collect();
        let locals_f = args.iter().copied().zip(params.iter().copied()).collect();
        let subst_f = self.infer_subst_ctxt(&locations_f, &locals_f);
        self.env_incl(
            &subst_f.apply(self.cx, locations_f),
            &subst_f.apply(self.cx, locals_f),
        );

        // Update context after function call
        let fresh = Local(Symbol::intern("$")); // FIXME
        for arg in args {
            self.uninit(&Place::from(*arg))
        }
        for (location, typ) in out_heap {
            self.insert_location(
                subst_f.apply(self.cx, *location),
                subst_f.apply(self.cx, typ),
            )
        }
        self.insert_local(fresh, out_ty);
        fresh
    }

    pub fn check_jump(&self, cont: &Cont<'_, 'lr>, args: &[Local]) {
        let locations = cont.locations_ctxt();
        let locals = cont.locals_ctxt(args).unwrap();
        let subst = self.infer_subst_ctxt(&locations, &locals);
        self.env_incl(
            &subst.apply(self.cx, locations),
            &subst.apply(self.cx, locals),
        );
    }

    fn env_incl(&self, locations: &LocationsCtxt<'lr>, locals: &LocalsCtxt) {
        for (_local, OwnRef(location)) in locals {
            self.subtype(
                locations,
                self.cx.mk_own_ref(*location),
                self.cx.mk_own_ref(*location),
            );
        }
    }

    fn subtype(&self, locations: &LocationsCtxt<'lr>, typ1: Ty<'lr>, typ2: Ty<'lr>) {
        match (typ1, typ2) {
            (TyS::Fn { .. }, TyS::Fn { .. }) => {}
            (TyS::OwnRef(location), TyS::OwnRef(location2)) => {
                assert!(location == location2);
                let typ1 = self.lookup_location(*location);
                let typ2 = locations[location];
                self.subtype(locations, typ1, typ2);
            }
            (TyS::Refine { .. }, TyS::Refine { .. }) => {
                println!("{:?}\n\t{:?} < {:?}\n", self, typ1, typ2)
            }
            (TyS::Tuple(_), TyS::Tuple(_)) => {
                // for ((x, t1), (y, t2)) in fields1.iter().zip(fields2) {}
            }
            (_, TyS::Uninit(_)) => {}
            _ => {}
        }
    }

    fn infer_subst_ctxt(&self, locations: &LocationsCtxt, locals: &LocalsCtxt) -> Subst {
        let mut h = Subst::new();
        for (local, OwnRef(location2)) in locals {
            let OwnRef(location1) = self.lookup_local(*local);
            h.extend(self.infer_subst_typ(
                locations,
                self.cx.mk_own_ref(location1),
                self.cx.mk_own_ref(*location2),
            ));
        }
        h
    }

    fn infer_subst_typ(&self, locations: &LocationsCtxt, typ1: Ty, typ2: Ty) -> Subst {
        match (typ1, typ2) {
            (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
                let mut subst =
                    self.infer_subst_typ(locations, self.lookup_location(*l1), locations[l2]);
                subst.insert(Var::Location(*l2), Var::Location(*l1));
                subst
            }
            _ => Subst::new(),
        }
    }
}

pub struct TypeCk<'a, 'b, 'lr> {
    tcx: TyCtxt<'lr>,
    kenv: &'a mut HashMap<Symbol, Cont<'b, 'lr>>,
    cx: &'lr LiquidRustCtxt<'lr>,
}

impl<'b, 'lr> TypeCk<'_, 'b, 'lr> {
    pub fn check(cx: &'lr LiquidRustCtxt<'lr>, fn_def: &FnDef<'lr>) {
        let mut kenv = HashMap::default();
        let env = vec![];
        kenv.insert(
            fn_def.ret,
            Cont {
                heap: &fn_def.out_heap,
                env: &env,
                params: vec![fn_def.out_ty],
            },
        );
        let mut checker = TypeCk {
            tcx: TyCtxt::from_fn_def(cx, fn_def),
            kenv: &mut kenv,
            cx,
        };
        checker.wt_fn_body(&fn_def.body);
    }

    fn wt_operand(&self, operand: &Operand) -> (Pred<'lr>, Ty<'lr>) {
        match operand {
            Operand::Deref(place) => self.tcx.lookup(place),
            Operand::Constant(c) => {
                let pred = self
                    .cx
                    .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_const(*c));
                (self.cx.mk_const(*c), self.cx.mk_refine(c.ty(), pred))
            }
        }
    }

    fn wt_binop(&mut self, op: BinOp, rhs: &Operand, lhs: &Operand) -> Ty<'lr> {
        let (p1, t1) = self.wt_operand(lhs);
        let (p2, t2) = self.wt_operand(rhs);
        if !t1.is_int() || !t2.is_int() {
            todo!("Cannot use operator `{:?}` with non integer types", op);
        }
        let pred = self
            .cx
            .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_binop(op, p1, p2));
        self.cx.mk_refine(op.ty(), pred)
    }

    fn wt_rvalue(&mut self, val: &Rvalue) -> Ty<'lr> {
        match val {
            Rvalue::Use(operand) => {
                let (pred, typ) = self.wt_operand(operand);
                if let Operand::Deref(place) = operand {
                    if !typ.is_copy() {
                        self.tcx.update(place, self.cx.mk_uninit(typ.size()));
                    }
                }
                self.selfify(pred, &typ)
            }
            Rvalue::BinaryOp(op, lhs, rhs) => self.wt_binop(*op, rhs, lhs),
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let t1 = self.wt_binop(*op, lhs, rhs);
                let t2 = self.cx.mk_refine(BasicType::Bool, self.cx.preds.tt);
                self.cx
                    .mk_tuple(&[(Field::nth(0), t1), (Field::nth(1), t2)])
            }
        }
    }

    fn wt_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::Let(x, layout) => {
                self.tcx.alloc(*x, layout);
            }
            Statement::Assign(place, rval) => {
                let (_, t1) = self.tcx.lookup(place);
                let t2 = self.wt_rvalue(rval);
                if t1.size() != t2.size() {
                    todo!();
                }
                self.tcx.update(place, t2);
            }
        }
    }

    fn wt_fn_body(&mut self, fn_body: &'b FnBody<'lr>) {
        match fn_body {
            FnBody::LetCont {
                name,
                heap,
                env,
                params,
                body,
                rest,
            } => {
                let cont = Cont {
                    heap,
                    env,
                    params: params.iter().map(|p| p.1).collect(),
                };
                let tcx = TyCtxt::new(
                    self.cx,
                    cont.locations_ctxt(),
                    env.iter().copied().chain(params.iter().copied()).collect(),
                );
                self.kenv.insert(*name, cont);
                let mut checker = TypeCk {
                    tcx,
                    kenv: self.kenv,
                    cx: self.cx,
                };
                checker.wt_fn_body(body);
                self.wt_fn_body(rest);
            }
            FnBody::Ite {
                discr: _,
                then_branch,
                else_branch,
            } => {
                // TODO: use the discriminant
                self.tcx.push_frame();
                self.wt_fn_body(then_branch);
                self.tcx.pop_frame();
                self.wt_fn_body(else_branch);
            }
            FnBody::Call { func, ret, args } => {
                let (_, typ) = self.tcx.lookup(func);
                match typ {
                    TyS::Fn {
                        in_heap,
                        params,
                        out_heap,
                        ret: out_ty,
                    } => {
                        let out_local = self
                            .tcx
                            .check_call(in_heap, params, out_heap, *out_ty, args);

                        self.tcx.check_jump(&self.kenv[ret], &[out_local]);
                    }
                    _ => {
                        todo!("not a function type");
                    }
                }
            }
            FnBody::Jump { target, args } => {
                self.tcx.check_jump(&self.kenv[target], args);
            }
            FnBody::Seq(statement, rest) => {
                self.wt_statement(statement);
                // println!("{:?}", self.tcx);
                self.wt_fn_body(rest);
            }
            FnBody::Abort => {}
        }
    }

    fn selfify(&self, pred: Pred<'lr>, typ: Ty<'lr>) -> Ty<'lr> {
        match typ {
            TyS::Refine { ty, .. } => {
                let r = self.cx.mk_binop(BinOp::Eq, self.cx.preds.nu, pred);
                self.cx.mk_refine(*ty, r)
            }
            _ => typ,
        }
    }
}

impl BinOp {
    pub fn ty(&self) -> BasicType {
        match self {
            BinOp::Add | BinOp::Sub => BasicType::Int,
            BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ge | BinOp::Gt => BasicType::Bool,
        }
    }
}

impl<'lr> Cont<'_, 'lr> {
    fn locals_ctxt(&self, args: &[Local]) -> Option<LocalsCtxt> {
        let mut ctxt: LocalsCtxt = self.env.iter().copied().collect();
        for (local, ownref) in args.iter().zip(&self.params) {
            if ctxt.contains_key(local) {
                return None;
            }
            ctxt.insert(*local, *ownref);
        }
        Some(ctxt)
    }
}

impl<'lr> Cont<'_, 'lr> {
    fn locations_ctxt(&self) -> LocationsCtxt<'lr> {
        self.heap.iter().copied().collect()
    }
}

struct Subst(HashMap<Var, Var>);

impl Subst {
    fn new() -> Self {
        Subst(HashMap::new())
    }

    fn extend(&mut self, subst: Subst) {
        self.0.extend(subst.0);
    }

    fn insert(&mut self, v1: Var, v2: Var) {
        self.0.insert(v1, v2);
    }

    fn get(&self, v: Var) -> Option<Var> {
        self.0.get(&v).copied()
    }

    fn apply<'lr, A: ApplySubst<'lr>>(&self, cx: &'lr LiquidRustCtxt<'lr>, x: A) -> A {
        x.apply_subst(cx, self)
    }
}

trait ApplySubst<'lr> {
    fn apply_subst(self, cx: &'lr LiquidRustCtxt<'lr>, subst: &Subst) -> Self;
}

impl<'lr> ApplySubst<'lr> for HashMap<Location, Ty<'lr>> {
    fn apply_subst(self, cx: &'lr LiquidRustCtxt<'lr>, subst: &Subst) -> Self {
        self.into_iter()
            .map(|(location, typ)| (subst.apply(cx, location), subst.apply(cx, typ)))
            .collect()
    }
}

impl<'lr> ApplySubst<'lr> for HashMap<Local, OwnRef> {
    fn apply_subst(self, cx: &'lr LiquidRustCtxt<'lr>, subst: &Subst) -> Self {
        self.into_iter()
            .map(|(local, OwnRef(location))| (local, OwnRef(subst.apply(cx, location))))
            .collect()
    }
}

impl<'lr> ApplySubst<'lr> for Ty<'lr> {
    fn apply_subst(self, cx: &'lr LiquidRustCtxt<'lr>, subst: &Subst) -> Self {
        match self {
            TyS::Fn { .. } => todo!(),
            TyS::OwnRef(_) => self,
            TyS::Refine { ty, pred } => cx.mk_refine(*ty, subst.apply(cx, pred)),
            TyS::Tuple(fields) => {
                let fields: Vec<(Field, Ty)> = fields
                    .iter()
                    .map(|(x, t)| (*x, subst.apply(cx, *t)))
                    .collect();
                cx.mk_tuple(&fields)
            }
            TyS::Uninit(_) => self,
        }
    }
}

impl<'lr> ApplySubst<'lr> for Pred<'lr> {
    fn apply_subst(self, cx: &'lr LiquidRustCtxt<'lr>, subst: &Subst) -> Self {
        match self {
            PredS::Constant(_) => self,
            PredS::Place { var, projection } => cx.mk_place(subst.apply(cx, *var), projection),
            PredS::BinaryOp(op, lhs, rhs) => {
                cx.mk_binop(*op, subst.apply(cx, lhs), subst.apply(cx, rhs))
            }
        }
    }
}

impl ApplySubst<'_> for Var {
    fn apply_subst(self, _cx: &LiquidRustCtxt, subst: &Subst) -> Self {
        subst.get(self).unwrap_or(self)
    }
}

impl ApplySubst<'_> for Location {
    fn apply_subst(self, _cx: &LiquidRustCtxt, subst: &Subst) -> Self {
        if let Some(Var::Location(l)) = subst.get(Var::Location(self)) {
            l
        } else {
            self
        }
    }
}
