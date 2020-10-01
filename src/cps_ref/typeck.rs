use std::collections::HashMap;

use super::{
    ast::*, constraint::Constraint, context::LiquidRustCtxt, subst::DeferredSubst, subst::Subst,
};

type LocalsMap = HashMap<Local, OwnRef>;
type LocationsMap<'lr> = HashMap<Location, Ty<'lr>>;
type Bindings<'lr> = Vec<(Location, Ty<'lr>)>;

struct TyCtxt<'lr> {
    cx: &'lr LiquidRustCtxt<'lr>,
    frames: Vec<CtxtFrame<'lr>>,
    curr_location: u32,
}

#[derive(Default)]
struct CtxtFrame<'lr> {
    locations: LocationsMap<'lr>,
    locals: LocalsMap,
}

impl<'lr> TyCtxt<'lr> {
    pub fn new(
        cx: &'lr LiquidRustCtxt<'lr>,
        locations: LocationsMap<'lr>,
        locals: LocalsMap,
    ) -> Self {
        let frame = CtxtFrame { locations, locals };
        Self {
            frames: vec![frame],
            cx,
            curr_location: 0,
        }
    }

    pub fn from_cont_def(cx: &'lr LiquidRustCtxt<'lr>, cont_def: &ContDef<'lr>) -> Self {
        Self::new(
            cx,
            cont_def.heap.iter().copied().collect(),
            cont_def
                .env
                .iter()
                .copied()
                .chain(cont_def.params.iter().copied())
                .collect(),
        )
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

    fn lookup_local(&self, x: Local) -> OwnRef {
        for frame in self.frames.iter().rev() {
            if let Some(ownref) = frame.locals.get(&x) {
                return *ownref;
            }
        }
        bug!("Cannot find local `{:?}`", x);
    }

    fn lookup_location(&self, l: Location) -> Ty<'lr> {
        for frame in self.frames.iter().rev() {
            if let Some(typ) = frame.locations.get(&l) {
                return typ;
            }
        }
        bug!("Cannot find location `{:?}`", l);
    }

    fn insert_location(&mut self, l: Location, typ: Ty<'lr>) {
        let frame = self.frames.last_mut().unwrap();
        frame.locations.insert(l, typ);
    }

    fn insert_local(&mut self, x: Local, ownref: OwnRef) {
        let frame = self.frames.last_mut().unwrap();
        frame.locals.insert(x, ownref);
    }

    pub fn uninit(&mut self, place: &Place) {
        let (_, t) = self.lookup(place);
        self.update(place, self.cx.mk_uninit(t.size()));
    }

    pub fn update(&mut self, place: &Place, typ: Ty<'lr>) -> (Location, Ty<'lr>) {
        let OwnRef(l) = self.lookup_local(place.local);
        let updated_typ = self
            .lookup_location(l)
            .update_at(self.cx, &place.projection, typ);
        let fresh_l = self.fresh_location();
        self.insert_location(fresh_l, updated_typ);
        self.insert_local(place.local, OwnRef(fresh_l));
        (fresh_l, updated_typ)
    }

    pub fn alloc(&mut self, x: Local, layout: &TypeLayout) {
        let fresh_l = self.fresh_location();
        self.insert_location(fresh_l, self.cx.mk_ty_for_layout(layout));
        self.insert_local(x, OwnRef(fresh_l));
    }

    fn fresh_location(&mut self) -> Location {
        let l = self.curr_location;
        self.curr_location += 1;
        Location(Symbol::intern(&format!("{}", l)))
    }

    pub fn check_call(
        &mut self,
        in_heap: &Heap<'lr>,
        params: &[OwnRef],
        out_heap: &Heap<'lr>,
        out_ty: OwnRef,
        args: &[Local],
        cont: &Cont<'_, 'lr>,
    ) -> Result<Constraint, SubtypingError<'lr>> {
        // Check against function arguments
        let locations_f = in_heap.iter().copied().collect();
        let locals_f = args.iter().copied().zip(params.iter().copied()).collect();
        let c1 = self.env_incl(locations_f, &locals_f)?;

        // Update context after function call
        let fresh_x = Local(Symbol::intern("$")); // FIXME
        for arg in args {
            self.uninit(&Place::from(*arg))
        }
        // FIXME: we are assuming all locations are fresh
        for (l, typ) in out_heap {
            self.insert_location(*l, typ);
        }
        self.insert_local(fresh_x, out_ty);

        let c2 =
            Constraint::from_bindings(out_heap.iter().copied(), self.check_jump(cont, &[fresh_x])?);
        Ok(Constraint::Conj(vec![c1, c2]))
    }

    pub fn check_jump(
        &mut self,
        cont: &Cont<'_, 'lr>,
        args: &[Local],
    ) -> Result<Constraint, SubtypingError<'lr>> {
        let locations = cont.locations_map();
        let locals = cont.locals_map(args).unwrap();
        self.env_incl(locations, &locals)
    }

    fn env_incl(
        &mut self,
        locations: LocationsMap<'lr>,
        locals: &LocalsMap,
    ) -> Result<Constraint, SubtypingError<'lr>> {
        let subst = self.infer_subst_ctxt(&locations, locals);
        let locations = DeferredSubst::new(subst, locations);
        let mut vec = vec![];
        for (x, OwnRef(l2)) in locals {
            let OwnRef(l1) = self.lookup_local(*x);
            let p = self.cx.mk_place(l1.into(), &[]);
            let typ1 = selfify(self.cx, p, self.lookup_location(l1)).into();
            let typ2 = locations.get(l2);
            vec.push(self.subtype(&locations, typ1, typ2)?);
        }
        Ok(Constraint::Conj(vec))
    }

    fn subtype(
        &mut self,
        locations: &DeferredSubst<LocationsMap<'lr>>,
        typ1: DeferredSubst<Ty<'lr>>,
        typ2: DeferredSubst<Ty<'lr>>,
    ) -> Result<Constraint, SubtypingError<'lr>> {
        let (subst1, typ1) = typ1.split();
        let (subst2, typ2) = typ2.split();
        let c = match (typ1, typ2) {
            (TyS::Fn { .. }, TyS::Fn { .. }) => todo!("implement function subtyping"),
            (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
                assert!(Some(Var::Location(*l1)) == subst2.get(Var::Location(*l2)));
                let p = self.cx.mk_place((*l1).into(), &[]);
                let typ1 = selfify(self.cx, p, self.lookup_location(*l1)).into();
                let typ2 = locations.get(l2);
                self.subtype(locations, typ1, typ2)?
            }
            (
                TyS::Refine {
                    ty: ty1,
                    pred: pred1,
                },
                TyS::Refine {
                    ty: ty2,
                    pred: pred2,
                },
            ) => {
                if ty1 != ty2 {
                    return Err(SubtypingError(typ1, typ2));
                }
                Constraint::from_subtype(
                    *ty1,
                    DeferredSubst::new(subst1, pred1),
                    DeferredSubst::new(subst2, pred2),
                )
            }
            (TyS::Tuple(fields1), TyS::Tuple(fields2)) => {
                if fields1.len() != fields2.len() {
                    return Err(SubtypingError(typ1, typ2));
                }
                let subst2 =
                    subst2.extend2(fields2.iter().map(|f| f.0), fields1.iter().map(|f| f.0));
                let mut iter = fields1.iter().zip(fields2).rev();
                if let Some(((_, t1), (_, t2))) = iter.next() {
                    let t1 = DeferredSubst::new(subst1.clone(), *t1);
                    let t2 = DeferredSubst::new(subst2.clone(), *t2);
                    let mut c = self.subtype(locations, t1, t2)?;
                    for ((x1, t1), (_, t2)) in iter {
                        let t1 = DeferredSubst::new(subst1.clone(), *t1);
                        let t2 = DeferredSubst::new(subst2.clone(), *t2);
                        c = Constraint::Conj(vec![
                            self.subtype(locations, t1.clone(), t2)?,
                            Constraint::from_binding(*x1, t1, c),
                        ]);
                    }
                    c
                } else {
                    Constraint::True
                }
            }
            (_, TyS::Uninit(_)) => Constraint::True,
            _ => return Err(SubtypingError(typ1, typ2)),
        };
        Ok(c)
    }

    fn infer_subst_ctxt(&self, locations: &LocationsMap, locals: &LocalsMap) -> Subst {
        let mut m = HashMap::new();
        for (x, OwnRef(l2)) in locals {
            let OwnRef(l1) = self.lookup_local(*x);
            m.extend(self.infer_subst_typ(
                locations,
                self.cx.mk_own_ref(l1),
                self.cx.mk_own_ref(*l2),
            ));
        }
        Subst::new(m)
    }

    fn infer_subst_typ(&self, locations: &LocationsMap, typ1: Ty, typ2: Ty) -> HashMap<Var, Var> {
        match (typ1, typ2) {
            (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
                let mut m =
                    self.infer_subst_typ(locations, self.lookup_location(*l1), locations[l2]);
                m.insert(Var::Location(*l2), Var::Location(*l1));
                m
            }
            _ => HashMap::new(),
        }
    }
}

pub struct TypeCk<'a, 'b, 'lr> {
    tcx: TyCtxt<'lr>,
    kenv: &'a mut HashMap<Symbol, Cont<'b, 'lr>>,
    cx: &'lr LiquidRustCtxt<'lr>,
}

impl<'b, 'lr> TypeCk<'_, 'b, 'lr> {
    pub fn cgen(cx: &'lr LiquidRustCtxt<'lr>, fn_def: &FnDef<'lr>) -> Constraint {
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
        Constraint::from_bindings(
            fn_def.heap.iter().copied(),
            checker.wt_fn_body(&fn_def.body),
        )
    }

    fn wt_operand(&mut self, operand: &Operand) -> (Pred<'lr>, Ty<'lr>, Bindings<'lr>) {
        match operand {
            Operand::Deref(place) => {
                let mut bindings = vec![];
                let (pred, typ) = self.tcx.lookup(place);
                if !typ.is_copy() {
                    bindings.push(self.tcx.update(place, self.cx.mk_uninit(typ.size())));
                }
                (pred, typ, bindings)
            }
            Operand::Constant(c) => {
                let pred = self
                    .cx
                    .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_const(*c));
                (
                    self.cx.mk_const(*c),
                    self.cx.mk_refine(c.ty(), pred),
                    vec![],
                )
            }
        }
    }

    fn wt_binop(&mut self, op: BinOp, rhs: &Operand, lhs: &Operand) -> (Ty<'lr>, Bindings<'lr>) {
        let (p1, t1, mut bindings1) = self.wt_operand(lhs);
        let (p2, t2, bindings2) = self.wt_operand(rhs);
        if !t1.is_int() || !t2.is_int() {
            todo!();
        }
        let ty = match op {
            BinOp::Add | BinOp::Sub => BasicType::Int,
            BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ge | BinOp::Gt => BasicType::Bool,
        };
        let pred = self
            .cx
            .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_binop(op, p1, p2));
        bindings1.extend(bindings2);
        (self.cx.mk_refine(ty, pred), bindings1)
    }

    fn wt_rvalue(&mut self, val: &Rvalue) -> (Ty<'lr>, Bindings<'lr>) {
        match val {
            Rvalue::Use(operand) => {
                let (p, typ, bindings) = self.wt_operand(operand);
                (selfify(self.cx, p, &typ), bindings)
            }
            Rvalue::BinaryOp(op, lhs, rhs) => self.wt_binop(*op, rhs, lhs),
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let (t1, bindings) = self.wt_binop(*op, lhs, rhs);
                let t2 = self.cx.mk_refine(BasicType::Bool, self.cx.preds.tt);
                let tuple = self
                    .cx
                    .mk_tuple(&[(Field::nth(0), t1), (Field::nth(1), t2)]);
                (tuple, bindings)
            }
            Rvalue::UnaryOp(op, operand) => {
                let (pred, typ, bindings) = self.wt_operand(operand);
                match (op, typ) {
                    (
                        UnOp::Not,
                        TyS::Refine {
                            ty: BasicType::Bool,
                            ..
                        },
                    ) => {
                        let t = self
                            .cx
                            .mk_refine(BasicType::Bool, self.cx.mk_unop(UnOp::Not, pred));
                        (t, bindings)
                    }
                    _ => {
                        todo!();
                    }
                }
            }
        }
    }

    fn wt_statement(&mut self, statement: &Statement) -> Bindings<'lr> {
        match statement {
            Statement::Let(x, layout) => {
                self.tcx.alloc(*x, layout);
                vec![]
            }
            Statement::Assign(place, rval) => {
                let (_, t1) = self.tcx.lookup(place);
                let (t2, mut bindings) = self.wt_rvalue(rval);
                if t1.size() != t2.size() {
                    todo!()
                }
                bindings.push(self.tcx.update(place, t2));
                bindings
            }
        }
    }

    fn wt_fn_body(&mut self, fn_body: &'b FnBody<'lr>) -> Constraint {
        match fn_body {
            FnBody::LetCont { def, rest } => {
                let cont = Cont::from(def);
                let tcx = TyCtxt::from_cont_def(self.cx, def);
                self.kenv.insert(def.name, cont);
                let mut checker = TypeCk {
                    tcx,
                    kenv: self.kenv,
                    cx: self.cx,
                };
                let c1 = Constraint::from_bindings(
                    def.heap.iter().copied(),
                    checker.wt_fn_body(&def.body),
                );
                let c2 = self.wt_fn_body(rest);
                Constraint::Conj(vec![c1, c2])
            }
            FnBody::Ite { discr, then, else_ } => {
                let (p, typ) = self.tcx.lookup(discr);
                match typ {
                    TyS::Refine {
                        ty: BasicType::Bool,
                        ..
                    } => {
                        self.tcx.push_frame();
                        let c1 = self.wt_fn_body(then);
                        self.tcx.pop_frame();
                        let c2 = self.wt_fn_body(else_);
                        Constraint::Conj(vec![
                            Constraint::guard(p, c1),
                            Constraint::guard(self.cx.mk_unop(UnOp::Not, p), c2),
                        ])
                    }
                    _ => todo!("not a boolean"),
                }
            }
            FnBody::Call { func, ret, args } => {
                let cont = &self.kenv[ret];
                let (_, typ) = self.tcx.lookup(func);
                match typ {
                    TyS::Fn {
                        in_heap,
                        params,
                        out_heap,
                        ret: out_ty,
                    } => {
                        let c = self
                            .tcx
                            .check_call(in_heap, params, out_heap, *out_ty, args, cont);
                        c.unwrap()
                    }
                    _ => {
                        todo!("not a function type");
                    }
                }
            }
            FnBody::Jump { target, args } => self.tcx.check_jump(&self.kenv[target], args).unwrap(),
            FnBody::Seq(statement, rest) => {
                let bindings = self.wt_statement(statement);
                Constraint::from_bindings(bindings.iter().copied(), self.wt_fn_body(rest))
            }
            FnBody::Abort => Constraint::True,
        }
    }
}
fn selfify<'lr>(cx: &'lr LiquidRustCtxt<'lr>, pred: Pred<'lr>, typ: Ty<'lr>) -> Ty<'lr> {
    match typ {
        TyS::Refine { ty, .. } => {
            let r = cx.mk_binop(BinOp::Eq, cx.preds.nu, pred);
            cx.mk_refine(*ty, r)
        }
        _ => typ,
    }
}

impl<'lr> Cont<'_, 'lr> {
    fn locals_map(&self, args: &[Local]) -> Option<LocalsMap> {
        let mut ctxt: LocalsMap = self.env.iter().copied().collect();
        for (local, ownref) in args.iter().zip(&self.params) {
            if ctxt.contains_key(local) {
                return None;
            }
            ctxt.insert(*local, *ownref);
        }
        Some(ctxt)
    }

    fn locations_map(&self) -> LocationsMap<'lr> {
        self.heap.iter().copied().collect()
    }
}

#[derive(Debug)]
struct SubtypingError<'lr>(Ty<'lr>, Ty<'lr>);
