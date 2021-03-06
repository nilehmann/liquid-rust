use std::collections::HashMap;

use super::{
    ast::*,
    constraint::{Constraint, Kvar, Sort},
    context::LiquidRustCtxt,
    subst::{DeferredSubst, Subst},
    utils::{Dict, OrderedHashMap, Scoped},
};
use thiserror::Error;

type LocalsMap = HashMap<Local, OwnRef>;
type LocationsMap<'lr> = OrderedHashMap<Location, Ty<'lr>>;
type Binding<'lr, T> = (T, Ty<'lr>);
type Bindings<'lr, T> = Vec<Binding<'lr, T>>;

struct TyCtxt<'lr> {
    cx: &'lr LiquidRustCtxt<'lr>,
    locations: Scoped<LocationsMap<'lr>>,
    locals: Vec<LocalsMap>,
    curr_location: u32,
    kenv: HashMap<Symbol, Cont<'lr>>,
    kvars: Vec<Kvar>,
}

impl<'lr> TyCtxt<'lr> {
    pub fn new(cx: &'lr LiquidRustCtxt<'lr>) -> Self {
        Self {
            cx,
            locations: Scoped::default(),
            locals: vec![],
            kenv: HashMap::new(),
            curr_location: 0,
            kvars: vec![],
        }
    }

    pub fn enter_fn_def(
        &mut self,
        fn_def: &FnDef<'lr>,
        mut act: impl for<'a> FnMut(&'a mut Self) -> Constraint,
    ) -> Constraint {
        let locations = self.insert_kvars_heap(&fn_def.heap);
        self.locations.push(locations);
        self.locals.push(fn_def.args.iter().copied().collect());

        let locations = self.insert_kvars_heap(&fn_def.out_heap);
        self.kenv.insert(
            fn_def.ret,
            Cont {
                heap: locations,
                env: vec![],
                params: vec![fn_def.out_ty],
            },
        );
        self.locations.push(OrderedHashMap::default());
        let c = act(self);
        self.locations.pop();
        self.locals.pop();
        Constraint::from_bindings(self.locations.pop().unwrap().into_iter(), c)
    }

    fn bindings<T: From<Location>>(&self) -> impl DoubleEndedIterator<Item = Binding<'lr, T>> + '_ {
        self.locations.iter().map(|(&l, &t)| (T::from(l), t))
    }

    pub fn enter_cont_def(
        &mut self,
        cont_def: &ContDef<'lr>,
        mut act: impl for<'a> FnMut(&'a mut Self) -> Constraint,
    ) -> Constraint {
        let locations = self.insert_kvars_heap(&cont_def.heap);
        self.locations.push(locations.clone());
        self.locals.push(
            cont_def
                .env
                .iter()
                .chain(cont_def.params.iter())
                .copied()
                .collect(),
        );
        self.kenv.insert(
            cont_def.name,
            Cont {
                heap: locations,
                env: cont_def.env.clone(),
                params: cont_def.params.iter().map(|p| p.1).collect(),
            },
        );
        self.locations.push(OrderedHashMap::default());
        let c = act(self);
        self.locations.pop();
        self.locals.pop();
        Constraint::from_bindings(self.locations.pop().unwrap().into_iter(), c)
    }

    pub fn enter_branch<T>(&mut self, mut act: impl for<'a> FnMut(&'a mut Self) -> T) -> T {
        self.locations.push(LocationsMap::new());
        self.locals.push(self.locals.last().unwrap().clone());
        let r = act(self);
        self.locals.pop();
        self.locations.pop();
        r
    }

    pub fn lookup(&self, place: &Place) -> (Pred<'lr>, Ty<'lr>) {
        self.lookup_(place.local, &place.projection)
    }

    fn lookup_(&self, local: Local, projection: &[Projection]) -> (Pred<'lr>, Ty<'lr>) {
        let OwnRef(mut location) = self.lookup_local(local).unwrap();
        let mut typ = self.lookup_location(location).unwrap();

        let mut v = Vec::new();
        for p in projection {
            match (typ, p) {
                (TyS::Tuple(fields), &Projection::Field(n)) => {
                    typ = fields[n as usize].1;
                    v.push(n);
                }
                (TyS::Ref(.., l), Projection::Deref) => {
                    v.clear();
                    location = *l;
                    typ = self.lookup_location(location).unwrap();
                }
                _ => bug!("{:?} {:?} {:?} {:?}", typ, local, projection, p),
            }
        }
        let pred = self.cx.mk_place(location.into(), &v);

        (pred, typ)
    }

    fn lookup_local(&self, x: Local) -> Option<OwnRef> {
        self.locals.last().and_then(|m| m.get(&x).copied())
    }

    fn lookup_location(&self, l: Location) -> Option<Ty<'lr>> {
        self.locations.get(&l).copied()
    }

    fn insert_location(&mut self, l: Location, typ: Ty<'lr>) {
        debug_assert!(self.lookup_location(l).is_none());
        self.locations.insert(l, typ);
    }

    fn insert_local(&mut self, x: Local, ownref: OwnRef) {
        self.locals.last_mut().unwrap().insert(x, ownref);
    }

    pub fn drop(
        &mut self,
        x: Local,
    ) -> Result<(Bindings<'lr, Location>, Constraint), TypeError<'lr>> {
        let OwnRef(l) = self.lookup_local(x).unwrap();
        let typ = self.lookup_location(l).unwrap();
        let (c, mut bindings) = self.drop_typ(typ)?;
        bindings.extend(self.update(&Place::from(x), self.cx.mk_uninit(typ.size())));
        Ok((bindings, c))
    }

    fn drop_typ(
        &mut self,
        typ: Ty<'lr>,
    ) -> Result<(Constraint, Bindings<'lr, Location>), TypeError<'lr>> {
        let mut constraints = vec![];
        let mut bindings = vec![];
        typ.try_walk(|_, typ| {
            match typ {
                TyS::Ref(BorrowKind::Mut, r, l) => {
                    let t = self.lookup_location(*l).unwrap();
                    if r.len() == 1 {
                        bindings.extend(self.update(&r[0], t));
                    } else {
                        let t_join = self
                            .replace_refine_with_kvars(t, &mut self.bindings::<Var>().collect());
                        constraints.push(inner_subtype(self.cx, &self.locations, t, t_join)?);
                        for p in r {
                            let (_, t2) = self.lookup(p);
                            constraints.push(inner_subtype(self.cx, &self.locations, t2, t_join)?);
                            bindings.extend(self.update(p, t_join));
                        }
                    }
                }
                _ => {}
            }
            Ok(())
        })?;
        Ok((Constraint::Conj(constraints), bindings))
    }

    fn replace_refine_with_kvars(
        &mut self,
        typ: Ty<'lr>,
        bindings: &mut Bindings<'lr, Var>,
    ) -> Ty<'lr> {
        match typ {
            TyS::Refine { ty, .. } => {
                let mut vars: Vec<Var> = vec![Var::Nu];
                vars.extend(bindings.iter().map(|&(x, _)| x));
                let kvar = self.fresh_kvar(*ty, bindings);
                self.cx
                    .mk_refine(*ty, self.cx.mk_pred(PredS::Kvar(kvar, vars)))
            }
            TyS::Tuple(fields) => {
                let fields: Vec<_> = fields
                    .iter()
                    .map(|&(f, t)| {
                        let t = self.replace_refine_with_kvars(t, bindings);
                        bindings.push((Var::from(f), t));
                        (f, t)
                    })
                    .collect();
                self.cx.mk_tuple(&fields)
            }
            TyS::Uninit(_)
            | TyS::Fn { .. }
            | TyS::OwnRef(_)
            | TyS::Ref(..)
            | TyS::RefineHole { .. } => typ,
        }
    }

    pub fn update(&mut self, place: &Place, new_typ: Ty<'lr>) -> Bindings<'lr, Location> {
        let OwnRef(l) = self.lookup_local(place.local).unwrap();
        let typ = self.lookup_location(l).unwrap();
        let (typ, mut bindings) =
            self.update_typ(Var::from(l), &mut vec![], typ, &place.projection, new_typ);
        let fresh = self.fresh_location();
        bindings.push((fresh, typ));
        for &(l, t) in &bindings {
            self.insert_location(l, t);
        }
        self.insert_local(place.local, OwnRef(fresh));
        bindings
    }

    fn update_typ(
        &mut self,
        var: Var,
        path: &mut Vec<u32>,
        typ: Ty<'lr>,
        proj: &[Projection],
        new_typ: Ty<'lr>,
    ) -> (Ty<'lr>, Vec<(Location, Ty<'lr>)>) {
        match (typ, proj) {
            (_, []) => {
                debug_assert!(typ.size() == new_typ.size());
                (new_typ, vec![])
            }
            (TyS::Tuple(fields), [Projection::Field(n), ..]) => {
                let mut fields = fields
                    .iter()
                    .enumerate()
                    .map(|(i, &(f, t))| {
                        path.push(i as u32);
                        let t = selfify(self.cx, var, path, t);
                        path.pop();
                        (f, t)
                    })
                    .collect::<Vec<_>>();
                path.push(*n);
                let f = &mut fields[*n as usize];
                let (t, bindings) = self.update_typ(var, path, f.1, &proj[1..], new_typ);
                f.1 = t;
                path.pop();
                (self.cx.mk_tuple(&fields), bindings)
            }
            (TyS::Ref(kind, r, l), [Projection::Deref, ..]) => {
                let referee = self.lookup_location(*l).unwrap();
                let (t, mut bindings) =
                    self.update_typ(Var::from(*l), &mut vec![], referee, &proj[1..], new_typ);
                let l = self.fresh_location();
                bindings.push((l, t));
                (self.cx.mk_ty(TyS::Ref(*kind, r.clone(), l)), bindings)
            }
            (TyS::OwnRef(_), [Projection::Deref, ..]) => todo!(),
            _ => bug!(""),
        }
    }

    pub fn alloc(&mut self, x: Local, layout: &TypeLayout) {
        debug_assert!(self.lookup_local(x).is_none());
        let fresh_l = self.fresh_location();
        self.insert_location(fresh_l, self.cx.mk_ty_for_layout(layout));
        self.insert_local(x, OwnRef(fresh_l));
    }

    pub fn borrow(
        &mut self,
        kind: BorrowKind,
        place: &Place,
    ) -> (Ty<'lr>, Bindings<'lr, Location>) {
        let (_, typ) = self.lookup(place);
        let l = self.fresh_location();
        self.insert_location(l, typ);
        (
            self.cx.mk_ty(TyS::Ref(kind, Region::new(place.clone()), l)),
            vec![(l, typ)],
        )
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
        ret: Symbol,
    ) -> Result<Constraint, TypeError<'lr>> {
        if args.len() != params.len() {
            return Err(TypeError::ArgCount);
        }
        // Check against function arguments
        let locations_f = self.insert_kvars_heap(&in_heap);
        let locals_f = args.iter().copied().zip(params.iter().copied()).collect();
        let c1 = env_incl(
            self.cx,
            &self.locations,
            self.locals.last().unwrap(),
            &locations_f,
            &locals_f,
        )?;

        // Update context after function call
        let fresh_x = Local(Symbol::intern("$")); // FIXME
        for &arg in args {
            let _ = self.drop(arg);
        }
        // FIXME: we are assuming all locations are fresh
        for (l, typ) in out_heap {
            self.insert_location(*l, typ);
        }
        self.insert_local(fresh_x, out_ty);

        let c2 =
            Constraint::from_bindings(out_heap.iter().copied(), self.check_jump(ret, &[fresh_x])?);
        Ok(Constraint::Conj(vec![c1, c2]))
    }

    pub fn check_jump(
        &mut self,
        ret: Symbol,
        args: &[Local],
    ) -> Result<Constraint, TypeError<'lr>> {
        let cont = &self.kenv[&ret];
        if args.len() != cont.params.len() {
            return Err(TypeError::ArgCount);
        }
        let locations1 = &self.locations;
        let locals1 = self.locals.last().unwrap();
        let locations2 = &cont.heap;
        let locals2 = &cont.locals_map(args)?;
        env_incl(self.cx, locations1, locals1, locations2, locals2)
    }

    fn insert_kvars_heap<'a>(&mut self, heap: &Heap<'lr>) -> LocationsMap<'lr> {
        let mut bindings = self.bindings().collect();
        heap.iter()
            .map(|&(l, t)| {
                let t = self.insert_kvars_typ(t, &mut bindings);
                bindings.push((Var::from(l), t));
                (l, t)
            })
            .collect()
    }

    fn insert_kvars_typ(&mut self, typ: Ty<'lr>, bindings: &mut Bindings<'lr, Var>) -> Ty<'lr> {
        match typ {
            TyS::Fn { .. } => todo!(),
            TyS::Tuple(fields) => {
                let fields: Vec<(Field, Ty)> = fields
                    .iter()
                    .map(|&(f, t)| {
                        let t = self.insert_kvars_typ(t, bindings);
                        bindings.push((Var::from(f), t));
                        (f, t)
                    })
                    .collect();
                bindings.truncate(bindings.len() - fields.len());
                self.cx.mk_tuple(&fields)
            }
            &TyS::RefineHole { ty } => {
                // liquid-fixpoint requires Nu to be the first argument
                let mut vars: Vec<Var> = vec![Var::Nu];
                vars.extend(bindings.iter().map(|&(x, _)| x));
                let kvar_n = self.fresh_kvar(ty, bindings);
                self.cx
                    .mk_refine(ty, self.cx.mk_pred(PredS::Kvar(kvar_n, vars)))
            }
            _ => typ,
        }
    }

    fn fresh_kvar(&mut self, nu_ty: BasicType, bindings: &Bindings<'lr, Var>) -> u32 {
        let n = self.kvars.len() as u32;
        let mut vars = vec![Sort::from(nu_ty)];
        vars.extend(bindings.iter().map(|&(_, t)| Sort::from(t)));
        self.kvars.push((n, vars));
        n
    }

    fn locals(&self) -> impl Iterator<Item = (&Local, &OwnRef)> {
        self.locals.last().unwrap().iter()
    }

    fn ownership(
        &self,
        kind: RefKind,
        place: &Place,
        reborrow_list: &mut Vec<Place>,
    ) -> Result<(), OwnershipError<'lr>> {
        for (&x, &OwnRef(l)) in self.locals() {
            let t = self.lookup_location(l).unwrap();
            t.try_walk(|path, typ| {
                match typ {
                    TyS::Ref(k, r, _) => {
                        if reborrow_list.iter().any(|p| p.equals(x, path)) {
                            return Ok(());
                        }

                        for p in r {
                            if place.overlaps(p) && (kind >= RefKind::Mut || k.is_mut()) {
                                return Err(OwnershipError::ConflictingBorrow(
                                    Place::new(x, path),
                                    typ,
                                ));
                            }
                        }
                    }
                    _ => {}
                }
                Ok(())
            })?;
        }

        for i in 0..place.projection.len() {
            match place.projection[i] {
                Projection::Field(_) => {}
                Projection::Deref => {
                    reborrow_list.push(Place::new(place.local, Vec::from(&place.projection[0..i])));
                    let (_, t) = self.lookup_(place.local, &place.projection[0..i]);
                    match t {
                        TyS::Ref(k, region, _) => {
                            if kind > *k {
                                return Err(OwnershipError::BehindRef(*k));
                            }
                            for p in region {
                                self.ownership(
                                    kind,
                                    &p.extend(&place.projection[i + 1..]),
                                    reborrow_list,
                                )?;
                            }
                            return Ok(());
                        }
                        TyS::OwnRef(_) => {
                            todo!();
                        }
                        _ => {}
                    }
                    reborrow_list.pop();
                }
            }
        }
        Ok(())
    }
}

pub struct TypeCk<'lr> {
    cx: &'lr LiquidRustCtxt<'lr>,
    errors: Vec<TypeError<'lr>>,
}

impl<'lr> TypeCk<'lr> {
    pub fn cgen(
        cx: &'lr LiquidRustCtxt<'lr>,
        fn_def: &FnDef<'lr>,
    ) -> Result<(Constraint, Vec<Kvar>), TypeErrors<'lr>> {
        let mut checker = Self { cx, errors: vec![] };
        let mut tcx = TyCtxt::new(cx);
        let c = tcx.enter_fn_def(fn_def, |tcx| checker.wt_fn_body(tcx, &fn_def.body));
        if checker.errors.is_empty() {
            Ok((c, tcx.kvars))
        } else {
            Err(TypeErrors(checker.errors))
        }
    }

    fn wt_operand(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        operand: &Operand,
    ) -> Result<(Pred<'lr>, Ty<'lr>, Bindings<'lr, Location>), TypeError<'lr>> {
        let r = match operand {
            Operand::Deref(place) => {
                let mut bindings = vec![];
                let (pred, typ) = tcx.lookup(place);
                if !typ.is_copy() {
                    tcx.ownership(RefKind::Owned, place, &mut vec![])
                        .map_err(|e| TypeError::CannotMove(place.clone(), e))?;
                    bindings.extend(tcx.update(place, self.cx.mk_uninit(typ.size())));
                }
                (pred, typ, bindings)
            }
            &Operand::Constant(Constant::Bool(b)) => {
                let c = self.cx.mk_const(ConstantP::Bool(b));
                let pred = self.cx.mk_binop(BinOp::Eq, self.cx.preds.nu, c);
                (c, self.cx.mk_refine(BasicType::Bool, pred), vec![])
            }
            &Operand::Constant(Constant::Int(i)) => {
                let c = self.cx.mk_const(ConstantP::Int(i));
                let pred = self.cx.mk_binop(BinOp::Eq, self.cx.preds.nu, c);
                (c, self.cx.mk_refine(BasicType::Int, pred), vec![])
            }
            Operand::Constant(Constant::Unit) => (self.cx.preds.tt, self.cx.types.unit, vec![]),
        };
        Ok(r)
    }

    fn wt_binop(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        op: BinOp,
        rhs: &Operand,
        lhs: &Operand,
    ) -> Result<(Ty<'lr>, Bindings<'lr, Location>), TypeError<'lr>> {
        let (p1, t1, mut bindings1) = self.wt_operand(tcx, lhs)?;
        let (p2, t2, bindings2) = self.wt_operand(tcx, rhs)?;
        bindings1.extend(bindings2);
        if !t1.is_int() || !t2.is_int() {
            return Err(TypeError::BinOpMismatch(op, t1, t2));
        }
        let (ty, pred) = match op {
            BinOp::Add | BinOp::Sub => (
                BasicType::Int,
                self.cx
                    .mk_binop(BinOp::Eq, self.cx.preds.nu, self.cx.mk_binop(op, p1, p2)),
            ),
            BinOp::Lt | BinOp::Le | BinOp::Eq | BinOp::Ge | BinOp::Gt => (
                BasicType::Bool,
                self.cx
                    .mk_iff(self.cx.preds.nu, self.cx.mk_binop(op, p1, p2)),
            ),
        };
        Ok((self.cx.mk_refine(ty, pred), bindings1))
    }

    fn wt_rvalue(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        val: &Rvalue,
    ) -> Result<(Ty<'lr>, Bindings<'lr, Location>), TypeError<'lr>> {
        let r = match val {
            Rvalue::Use(operand) => {
                let (p, typ, bindings) = self.wt_operand(tcx, operand)?;
                match p {
                    PredS::Place { var, projection } => (
                        selfify(self.cx, *var, &mut projection.clone(), &typ),
                        bindings,
                    ),
                    _ => (typ, bindings),
                }
            }
            Rvalue::BinaryOp(op, lhs, rhs) => self.wt_binop(tcx, *op, rhs, lhs)?,
            Rvalue::CheckedBinaryOp(op, lhs, rhs) => {
                let (t1, bindings) = self.wt_binop(tcx, *op, lhs, rhs)?;
                let t2 = self.cx.mk_refine(BasicType::Bool, self.cx.preds.tt);
                let tuple = self
                    .cx
                    .mk_tuple(&[(Field::nth(0), t1), (Field::nth(1), t2)]);
                (tuple, bindings)
            }
            Rvalue::UnaryOp(op, operand) => {
                let (pred, typ, bindings) = self.wt_operand(tcx, operand)?;
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
                        return Err(TypeError::UnOpMismatch(*op, typ));
                    }
                }
            }
            Rvalue::Ref(kind, place) => {
                tcx.ownership(RefKind::from(*kind), place, &mut vec![])
                    .map_err(|e| TypeError::CannotBorrow(place.clone(), *kind, e))?;
                tcx.borrow(*kind, place)
            }
        };
        Ok(r)
    }

    fn wt_statement(
        &mut self,
        tcx: &mut TyCtxt<'lr>,
        statement: &Statement,
    ) -> Result<(Bindings<'lr, Location>, Constraint), TypeError<'lr>> {
        Ok(match statement {
            Statement::Let(x, layout) => {
                tcx.alloc(*x, layout);
                (vec![], Constraint::True)
            }
            Statement::Assign(place, rval) => {
                let (_, t1) = tcx.lookup(place);
                let (t2, mut bindings) = self.wt_rvalue(tcx, rval)?;
                tcx.ownership(RefKind::Mut, place, &mut vec![])
                    .map_err(|e| TypeError::CannotAssign(place.clone(), e))?;
                if t1.size() != t2.size() {
                    return Err(TypeError::SizeMismatch(t1, t2));
                }
                bindings.extend(tcx.update(place, t2));
                (bindings, Constraint::True)
            }
            &Statement::Drop(x) => {
                let place = Place::from(x);
                tcx.ownership(RefKind::Owned, &place, &mut vec![])
                    .map_err(|e| TypeError::CannotMove(place, e))?;
                tcx.drop(x)?
            }
            Statement::Debug => {
                println!("{}", tcx);
                (vec![], Constraint::True)
            }
        })
    }

    fn wt_fn_body(&mut self, tcx: &mut TyCtxt<'lr>, fn_body: &FnBody<'lr>) -> Constraint {
        match fn_body {
            FnBody::LetCont { def, rest } => {
                let c1 = tcx.enter_cont_def(def, |tcx| self.wt_fn_body(tcx, &def.body));
                let c2 = self.wt_fn_body(tcx, rest);
                Constraint::Conj(vec![c1, c2])
            }
            FnBody::Ite { discr, then, else_ } => {
                let (p, typ) = tcx.lookup(discr);
                match typ {
                    TyS::Refine {
                        ty: BasicType::Bool,
                        ..
                    } => {
                        let c1 = tcx.enter_branch(|tcx| self.wt_fn_body(tcx, then));
                        let c2 = self.wt_fn_body(tcx, else_);
                        Constraint::Conj(vec![
                            Constraint::guard(p, c1),
                            Constraint::guard(self.cx.mk_unop(UnOp::Not, p), c2),
                        ])
                    }
                    _ => {
                        self.errors.push(TypeError::NotBool(typ));
                        Constraint::Err
                    }
                }
            }
            FnBody::Call { func, ret, args } => {
                let (_, typ) = tcx.lookup(func);
                match typ {
                    TyS::Fn {
                        in_heap,
                        params,
                        out_heap,
                        ret: out_ty,
                    } => match tcx.check_call(in_heap, params, out_heap, *out_ty, args, *ret) {
                        Ok(c) => c,
                        Err(err) => {
                            self.errors.push(err);
                            Constraint::Err
                        }
                    },
                    _ => {
                        self.errors.push(TypeError::NotFun(typ));
                        Constraint::Err
                    }
                }
            }
            FnBody::Jump { target, args } => match tcx.check_jump(*target, args) {
                Ok(c) => c,
                Err(err) => {
                    self.errors.push(err);
                    Constraint::Err
                }
            },
            FnBody::Seq(statement, rest) => match self.wt_statement(tcx, statement) {
                Ok((bindings, c)) => Constraint::Conj(vec![
                    Constraint::from_bindings(bindings.iter().copied(), self.wt_fn_body(tcx, rest)),
                    c,
                ]),
                Err(err) => {
                    self.errors.push(err);
                    Constraint::Err
                }
            },
            FnBody::Abort => Constraint::True,
        }
    }
}
fn selfify<'lr>(
    cx: &'lr LiquidRustCtxt<'lr>,
    var: Var,
    proj: &mut Vec<u32>,
    typ: Ty<'lr>,
) -> Ty<'lr> {
    match typ {
        TyS::Refine { ty, .. } => {
            let r = cx.mk_binop(BinOp::Eq, cx.preds.nu, cx.mk_place(var, &proj));
            cx.mk_refine(*ty, r)
        }
        TyS::Tuple(fields) => {
            let fields = fields
                .iter()
                .enumerate()
                .map(|(i, &(f, t))| {
                    proj.push(i as u32);
                    let t = selfify(cx, var, proj, t);
                    proj.pop();
                    (f, t)
                })
                .collect::<Vec<_>>();
            cx.mk_tuple(&fields)
        }
        _ => typ,
    }
}

impl<'lr> Cont<'lr> {
    fn locals_map(&self, args: &[Local]) -> Result<LocalsMap, TypeError<'lr>> {
        debug_assert!(args.len() == self.params.len());
        let mut ctxt: LocalsMap = self.env.iter().copied().collect();
        for (local, ownref) in args.iter().zip(&self.params) {
            if ctxt.contains_key(local) {
                return Err(TypeError::DupLocal(*local));
            }
            ctxt.insert(*local, *ownref);
        }
        Ok(ctxt)
    }
}

struct Cont<'lr> {
    pub heap: LocationsMap<'lr>,
    pub env: Env,
    pub params: Vec<OwnRef>,
}

#[derive(Error, Debug)]
pub struct TypeErrors<'lr>(Vec<TypeError<'lr>>);

impl<'lr> std::fmt::Display for TypeErrors<'lr> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self
            .0
            .iter()
            .map(|e| format!("error: {}", e))
            .collect::<Vec<_>>()
            .join("\n\n");
        write!(f, "{}\n", s)
    }
}

#[derive(Debug)]
pub enum OwnershipError<'lr> {
    ConflictingBorrow(Place, Ty<'lr>),
    BehindRef(BorrowKind),
}

impl std::fmt::Display for OwnershipError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OwnershipError::BehindRef(k) => write!(f, "is behind a {} reference", k),
            OwnershipError::ConflictingBorrow(p, t) => write!(
                f,
                "there is a conficting borrow at place `{}` with type {}",
                p, t
            ),
        }
    }
}

#[derive(Error, Debug)]
pub enum TypeError<'lr> {
    #[error("{0} is not a subtype of {1}")]
    SubtypingError(Ty<'lr>, Ty<'lr>),
    #[error("{0} does not have the same size than {1}")]
    SizeMismatch(Ty<'lr>, Ty<'lr>),
    #[error("duplicate local {0}")]
    DupLocal(Local),
    #[error("invalid operator application {0} for values of type {1} and {2}")]
    BinOpMismatch(BinOp, Ty<'lr>, Ty<'lr>),
    #[error("invalid operator application {0} for value of type {1}")]
    UnOpMismatch(UnOp, Ty<'lr>),
    #[error("{0} is not a function type")]
    NotFun(Ty<'lr>),
    #[error("{0} is not a boolean type")]
    NotBool(Ty<'lr>),
    #[error("wrong number of arguments")]
    ArgCount,

    #[error("cannot borrow `{0}` as {1} because {2}")]
    CannotBorrow(Place, BorrowKind, OwnershipError<'lr>),
    #[error("cannot assign to `{0}` because {1}")]
    CannotAssign(Place, OwnershipError<'lr>),
    #[error("cannot move out of `{0}` because {1}")]
    CannotMove(Place, OwnershipError<'lr>),
}

fn env_incl<'lr>(
    cx: &'lr LiquidRustCtxt<'lr>,
    locations1: &Scoped<LocationsMap<'lr>>,
    locals1: &LocalsMap,
    locations2: &LocationsMap<'lr>,
    locals2: &LocalsMap,
) -> Result<Constraint, TypeError<'lr>> {
    let subst = infer_subst_ctxt(locations1, locals1, locations2, locals2);
    let locations2 = &DeferredSubst::new(subst, locations2);
    let mut vec = vec![];
    for (x, OwnRef(l2)) in locals2 {
        let OwnRef(l1) = locals1[x];
        let typ1 = selfify(cx, Var::from(l1), &mut vec![], locations1[l1]);
        let typ2 = locations2.get(l2);
        vec.push(subtype(cx, locations1, typ1.into(), locations2, typ2)?);
    }
    Ok(Constraint::Conj(vec))
}

fn subtype<'lr>(
    cx: &'lr LiquidRustCtxt<'lr>,
    locations1: &Scoped<LocationsMap<'lr>>,
    typ1: DeferredSubst<Ty<'lr>>,
    locations2: &DeferredSubst<&LocationsMap<'lr>>,
    typ2: DeferredSubst<Ty<'lr>>,
) -> Result<Constraint, TypeError<'lr>> {
    let (subst1, typ1) = typ1.split();
    let (subst2, typ2) = typ2.split();
    let c = match (typ1, typ2) {
        (TyS::Fn { .. }, TyS::Fn { .. }) => todo!("implement function subtyping"),
        (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
            let typ1 = selfify(cx, Var::from(*l1), &mut vec![], locations1[*l1]);
            let typ2 = locations2.get(l2);
            subtype(cx, locations1, typ1.into(), locations2, typ2)?
        }
        (TyS::Ref(kind1, r1, l1), TyS::Ref(kind2, r2, l2)) => {
            if !r1.subset_of(r2) {
                todo!("{:?} {:?}", r1, r2)
            }
            if kind1 != kind2 {
                todo!("{:?} {:?}", kind1, kind2)
            }
            let typ1 = selfify(cx, Var::from(*l1), &mut vec![], locations1[*l1]);
            let typ2 = locations2.get(l2);
            subtype(cx, locations1, typ1.into(), locations2, typ2)?
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
                return Err(TypeError::SubtypingError(typ1, typ2));
            }
            Constraint::from_subtype(
                *ty1,
                DeferredSubst::new(subst1, pred1),
                DeferredSubst::new(subst2, pred2),
            )
        }
        (TyS::Tuple(fields1), TyS::Tuple(fields2)) => {
            if fields1.len() != fields2.len() {
                return Err(TypeError::SubtypingError(typ1, typ2));
            }
            let subst2 = subst2.extend2(fields2.iter().map(|f| f.0), fields1.iter().map(|f| f.0));
            let mut iter = fields1.iter().zip(fields2).rev();
            if let Some(((_, t1), (_, t2))) = iter.next() {
                let t1 = DeferredSubst::new(subst1.clone(), *t1);
                let t2 = DeferredSubst::new(subst2.clone(), *t2);
                let mut c = subtype(cx, locations1, t1, locations2, t2)?;
                for ((x1, t1), (_, t2)) in iter {
                    let t1 = DeferredSubst::new(subst1.clone(), *t1);
                    let t2 = DeferredSubst::new(subst2.clone(), *t2);
                    c = Constraint::Conj(vec![
                        subtype(cx, locations1, t1.clone(), locations2, t2)?,
                        Constraint::from_binding(*x1, t1, c),
                    ]);
                }
                c
            } else {
                Constraint::True
            }
        }
        (_, TyS::Uninit(_)) => Constraint::True,
        _ => return Err(TypeError::SubtypingError(typ1, typ2)),
    };
    Ok(c)
}

fn inner_subtype<'lr>(
    cx: &'lr LiquidRustCtxt<'lr>,
    locations: &Scoped<LocationsMap<'lr>>,
    typ1: Ty<'lr>,
    typ2: Ty<'lr>,
) -> Result<Constraint, TypeError<'lr>> {
    let c = match (typ1, typ2) {
        (TyS::Fn { .. }, TyS::Fn { .. }) => todo!("implement function subtyping"),
        (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
            let typ1 = selfify(cx, Var::from(*l1), &mut vec![], locations[*l1]);
            let typ2 = locations[*l2];
            inner_subtype(cx, locations, typ1.into(), typ2)?
        }
        (TyS::Ref(kind1, r1, l1), TyS::Ref(kind2, r2, l2)) => {
            if !r1.subset_of(r2) {
                todo!("")
            }
            if kind1 != kind2 {
                todo!("")
            }
            let typ1 = selfify(cx, Var::from(*l1), &mut vec![], locations[*l1]);
            let typ2 = locations[*l2];
            inner_subtype(cx, locations, typ1, typ2)?
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
                return Err(TypeError::SubtypingError(typ1, typ2));
            }
            Constraint::from_subtype(
                *ty1,
                DeferredSubst::empty(pred1),
                DeferredSubst::empty(pred2),
            )
        }
        (TyS::Tuple(fields1), TyS::Tuple(fields2)) => {
            if fields1.len() != fields2.len() {
                return Err(TypeError::SubtypingError(typ1, typ2));
            }
            let mut iter = fields1.iter().zip(fields2).rev();
            if let Some((&(_, t1), &(_, t2))) = iter.next() {
                let mut c = inner_subtype(cx, locations, t1, t2)?;
                for (&(x1, t1), &(_, t2)) in iter {
                    c = Constraint::Conj(vec![
                        inner_subtype(cx, locations, t1, t2)?,
                        Constraint::from_binding(x1, t1, c),
                    ]);
                }
                c
            } else {
                Constraint::True
            }
        }
        (_, TyS::Uninit(_)) => Constraint::True,
        _ => return Err(TypeError::SubtypingError(typ1, typ2)),
    };
    Ok(c)
}

fn infer_subst_ctxt<'lr>(
    locations1: &Scoped<LocationsMap<'lr>>,
    locals1: &LocalsMap,
    locations2: &LocationsMap<'lr>,
    locals2: &LocalsMap,
) -> Subst {
    let mut v = Vec::new();
    for (x, &OwnRef(l2)) in locals2 {
        let OwnRef(l1) = locals1[x];
        infer_subst_typ(
            locations1,
            &TyS::OwnRef(l1),
            locations2,
            &TyS::OwnRef(l2),
            &mut v,
        );
    }
    Subst::from(v)
}

fn infer_subst_typ(
    locations1: &Scoped<LocationsMap>,
    typ1: Ty,
    locations2: &LocationsMap,
    typ2: Ty,
    v: &mut Vec<(Var, Var)>,
) {
    match (typ1, typ2) {
        (TyS::OwnRef(l1), TyS::OwnRef(l2)) => {
            infer_subst_typ(locations1, locations1[*l1], locations2, locations2[l2], v);
            v.push((Var::Location(*l2), Var::Location(*l1)));
        }
        _ => {}
    }
}

#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone)]
enum RefKind {
    Shared,
    Mut,
    Owned,
}

impl From<BorrowKind> for RefKind {
    fn from(kind: BorrowKind) -> Self {
        match kind {
            BorrowKind::Shared => RefKind::Shared,
            BorrowKind::Mut => RefKind::Mut,
        }
    }
}

impl std::cmp::PartialEq<BorrowKind> for RefKind {
    fn eq(&self, other: &BorrowKind) -> bool {
        match (self, other) {
            (RefKind::Mut, BorrowKind::Mut) | (RefKind::Shared, BorrowKind::Shared) => true,
            _ => false,
        }
    }
}

impl std::cmp::PartialOrd<BorrowKind> for RefKind {
    fn partial_cmp(&self, other: &BorrowKind) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (RefKind::Shared, BorrowKind::Shared) => Some(std::cmp::Ordering::Equal),
            (RefKind::Shared, BorrowKind::Mut) => Some(std::cmp::Ordering::Less),
            (RefKind::Mut, BorrowKind::Shared) => Some(std::cmp::Ordering::Greater),
            (RefKind::Mut, BorrowKind::Mut) => Some(std::cmp::Ordering::Equal),
            (RefKind::Owned, BorrowKind::Shared) => Some(std::cmp::Ordering::Greater),
            (RefKind::Owned, BorrowKind::Mut) => Some(std::cmp::Ordering::Greater),
        }
    }
}

impl std::fmt::Display for TyCtxt<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let locations = self
            .bindings::<Location>()
            .map(|(x, t)| format!("{}: {}", x, t))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[ {} ]\n", locations)?;
        let locals = self
            .locals
            .last()
            .unwrap_or(&HashMap::new())
            .iter()
            .map(|(x, t)| format!("{}: {}", x, t))
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "[ {} ]\n", locals)?;
        Ok(())
    }
}
