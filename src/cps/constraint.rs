use super::ast::*;

use crate::context::ArenaInterner;

use rsmt2::{print::Expr2Smt, Solver};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constraint<'cx> {
    Pred(&'cx Pred<'cx>),
    Conj(&'cx Constraint<'cx>, &'cx Constraint<'cx>),
    Forall {
        ident: Symbol,
        ty: BasicType,
        hyp: &'cx Pred<'cx>,
        con: &'cx Constraint<'cx>,
    },
    Implies(&'cx Pred<'cx>, &'cx Constraint<'cx>),
}

/// A typing environment is a map from names to types
pub type TEnv<'cx> = HashMap<Local, &'cx Type<'cx>>;

/// A continuation environment is a map from names to lists of args
pub type KEnv<'cx> = HashMap<Local, &'cx [Tydent<'cx>]>;

pub struct ConstraintGen<'cx> {
    tenv: TEnv<'cx>,
    kenv: KEnv<'cx>,

    cps_arena: &'cx CpsArena<'cx>,
    cgen_arena: &'cx ArenaInterner<'cx, Constraint<'cx>>,

    always: &'cx Constraint<'cx>,
}

impl<'cx> ConstraintGen<'cx> {
    pub fn new(
        cps_arena: &'cx CpsArena<'cx>,
        cgen_arena: &'cx ArenaInterner<'cx, Constraint<'cx>>,
    ) -> Self {
        let p = cps_arena
            .preds
            .intern(Pred::Op(Operand::Lit(Literal::Bool(true))));
        let always = cgen_arena.intern(Constraint::Pred(p));
        ConstraintGen {
            tenv: HashMap::new(),
            kenv: HashMap::new(),

            cgen_arena,
            cps_arena,

            always,
        }
    }

    fn bind1(
        &self,
        name: Local,
        ty: &'cx Type<'cx>,
        rest: &'cx Constraint<'cx>,
    ) -> &'cx Constraint<'cx> {
        match ty {
            Type::Reft { ident, ty, pred } => self.cgen_arena.intern(Constraint::Forall {
                ident: name,
                ty: *ty,
                hyp: pred.run_subst(self.cps_arena, &Subst::new(&[*ident], &[name])),
                con: rest,
            }),
            Type::Prod(ptys) => self.bind(&ptys, rest),
            _ => rest,
        }
    }

    /// Sometimes, we want to create an implication constraint where the hypothesis is
    /// "we have variables x_i of type T_i", where T_i is some refinement type, and the
    /// conclusion can mention these variables. A Forall constraint allows us to bind
    /// these variables in the hypothesis so that the conclusion can use them, but
    /// a Forall constraint only keeps track of the BasicType of a variable; naively
    /// constructing a Forall Constraint would throw away our predicates.
    ///
    /// bind creates Forall Constraints such that refinements over Refts are preserved.
    fn bind(&self, tyds: &'cx [Tydent<'cx>], rest: &'cx Constraint<'cx>) -> &'cx Constraint<'cx> {
        let mut res = rest;

        for tyd in tyds.iter().rev() {
            res = self.bind1(tyd.ident, &tyd.reft, res);
        }

        res
    }

    /// Produces a subtyping constraint, where the constraint is such that
    /// the first type is a subtype of the second.
    ///
    /// If no valid constraint could be produced, returns None
    fn subtype(&self, a: DeferType<'cx>, b: DeferType<'cx>) -> Option<&'cx Constraint<'cx>> {
        match (a, b) {
            (
                d1
                @
                DeferType {
                    reft: Type::Reft { .. },
                    ..
                },
                d2
                @
                DeferType {
                    reft: Type::Reft { .. },
                    ..
                },
            ) => {
                let t1 = d1.run_subst(self.cps_arena);
                let t2 = d2.run_subst(self.cps_arena);

                match (t1, t2) {
                    (
                        Type::Reft {
                            ident: ia,
                            ty: ba,
                            pred: pa,
                        },
                        Type::Reft {
                            ident: ib,
                            ty: bb,
                            pred: pb,
                        },
                    ) => {
                        // If we're checking two scalar types, we check if a value of former's base
                        // type would be assignable to the latter's base type.
                        if ba.assignable_to(*bb) {
                            let ibs = &[*ib];
                            let ias = &[*ia];
                            let s = Subst::new(ibs, ias);
                            Some(self.cgen_arena.intern(
                                Constraint::Forall {
                                    ident: *ia,
                                    ty: *ba,
                                    hyp: pa,
                                    con:
                                        self.cgen_arena.intern(Constraint::Pred(
                                            pb.run_subst(self.cps_arena, &s),
                                        )),
                                },
                            ))
                        } else {
                            None
                        }
                    }
                    _ => unreachable!(),
                }
            }
            (
                DeferType {
                    reft: Type::Fn { args: a1s, ret: r1 },
                    subst: s1,
                },
                DeferType {
                    reft: Type::Fn { args: a2s, ret: r2 },
                    subst: s2,
                },
            ) => {
                // We first create a constraint on the return types of the fns
                let a1is = a1s.iter().map(|x| x.ident).collect::<Vec<Symbol>>();
                let a2is = a2s.iter().map(|x| x.ident).collect::<Vec<Symbol>>();

                let s = Subst::new(&a1is, &a2is);

                let mut res = self.subtype(
                    r1.reft.extend_subst(self.cps_arena, s1, &s),
                    r2.reft.as_deferred(s2),
                )?;

                for (a1, a2) in a1s.into_iter().zip(a2s.into_iter()).rev() {
                    let sub = self.subtype(
                        a2.reft.as_deferred(s2),
                        a1.reft.extend_subst(self.cps_arena, s2, &s),
                    )?;
                    // TODO: self.cps_arena.tyd_args.alloc(vec![*a2]) sucks
                    res = self.bind(
                        self.cps_arena.tyd_args.alloc(vec![*a2]),
                        self.cgen_arena.intern(Constraint::Conj(res, sub)),
                    );
                }

                Some(res)
            }
            _ => None,
        }
    }

    pub fn synth(&self, tenv: &TEnv<'cx>, rval: RValue<'cx>) -> Option<&'cx Type<'cx>> {
        match rval {
            RValue::Op(Operand::Lit(l)) => {
                let v = Local::intern("_v");
                let res = Type::Reft {
                    ident: v,
                    ty: match l {
                        Literal::Bool(_) => BasicType::Bool,
                        Literal::Int(_) => BasicType::Int(IntTy::I32),
                    },
                    pred: self.cps_arena.preds.intern(Pred::Binary(
                        PredBinOp::Eq,
                        Pred::from_local(self.cps_arena, v),
                        Pred::from_op(self.cps_arena, Operand::Lit(l)),
                    )),
                };

                Some(self.cps_arena.refts.intern(res))
            }
            RValue::Op(Operand::Path(p)) => {
                let mut ty = tenv.get(&p.ident)?;

                for proj in p.projs {
                    if let Type::Prod(ts) = ty {
                        ty = &ts.get(*proj)?.reft;
                    } else {
                        return None;
                    }
                }

                Some(ty)
            }
            RValue::Binary(RBinOp::CheckedAdd, o1, o2) => {
                let loc = Local::intern("_v");
                let tyd1 = Tydent {
                    ident: loc,
                    reft: self.cps_arena.refts.intern(Type::Reft {
                        ident: loc,
                        // TODO: proper int type recognition
                        ty: BasicType::Int(IntTy::I128),
                        pred: self.cps_arena.preds.intern(Pred::Binary(
                            PredBinOp::Eq,
                            Pred::from_local(self.cps_arena, loc),
                            self.cps_arena.preds.intern(Pred::Binary(
                                PredBinOp::Add,
                                Pred::from_op(self.cps_arena, o1),
                                Pred::from_op(self.cps_arena, o2),
                            )),
                        )),
                    }),
                };
                let tyd2 = Tydent {
                    ident: Local::intern("_w"),
                    reft: Type::from_basic(self.cps_arena, BasicType::Bool),
                };
                let args = self.cps_arena.tyd_args.alloc(vec![tyd1, tyd2]);
                Some(self.cps_arena.refts.intern(Type::Prod(args)))
            }
            RValue::Binary(cmp, o1, o2) => {
                let loc = Local::intern("_v");
                let reft = Type::Reft {
                    ident: loc,
                    ty: BasicType::Bool,
                    pred: self.cps_arena.preds.intern(Pred::Binary(
                        PredBinOp::Eq,
                        Pred::from_local(self.cps_arena, loc),
                        self.cps_arena.preds.intern(Pred::Binary(
                            cmp.into(),
                            Pred::from_op(self.cps_arena, o1),
                            Pred::from_op(self.cps_arena, o2),
                        )),
                    )),
                };
                Some(self.cps_arena.refts.intern(reft))
            }
        }
    }

    pub fn check_fns(&mut self, fs: Vec<FnDef<'cx>>) -> Option<()> {
        let mut solver = Solver::default(()).expect("couldn't create solver");

        let cs = self.cgen_fns(fs)?;

        for c in cs {
            let _ = c.expr_to_smt2(&mut std::io::stdout(), ());
            solver.assert(&c).expect("failed to assert");
            if solver.check_sat().expect("during check sat") {
                ()
            } else {
                panic!("expected sat, got unsat")
            }
        }

        Some(())
    }

    pub fn cgen_fns(&mut self, fs: Vec<FnDef<'cx>>) -> Option<Vec<&'cx Constraint<'cx>>> {
        // For each function we have, we check it, then add its type
        // to our environment
        let mut cons = vec![];

        for f in fs {
            let args = f.args;
            let ret = f.ret;
            let name = f.name;
            cons.push(self.cgen_fn(f)?);
            self.tenv
                .insert(name, self.cps_arena.refts.intern(Type::Fn { args, ret }));
        }

        Some(cons)
    }

    pub fn cgen_fn(&mut self, f: FnDef<'cx>) -> Option<&'cx Constraint<'cx>> {
        // We first add all the arguments of the function to the TEnv.
        let mut prevs = vec![];
        for arg in f.args {
            prevs.push((arg.ident, self.tenv.insert(arg.ident, arg.reft)));
        }

        // We then add the result cont to the environment
        let prevk = self
            .kenv
            .insert(f.cont, self.cps_arena.tyd_args.alloc(vec![f.ret]));

        // Actually do codegen for this fn
        let mut res = self.cgen(f.body)?;

        // Finally, remove what we added to the env, replacing them with
        // their prev values if needed.
        if let Some(pk) = prevk {
            self.kenv.insert(f.cont, pk);
        } else {
            self.kenv.remove(&f.cont);
        }

        for (idn, reft) in prevs.into_iter().rev() {
            // get our reft and bind it in the constraint
            res = self.bind1(idn, &self.tenv[&idn], res);

            if let Some(r) = reft {
                self.tenv.insert(idn, r);
            } else {
                self.tenv.remove(&idn);
            }
        }

        Some(res)
    }

    pub fn cgen(&mut self, body: &'cx FuncBody<'cx>) -> Option<&'cx Constraint<'cx>> {
        match body {
            FuncBody::Let(l, rv, fb) => {
                let ty = self.synth(&self.tenv, *rv)?;
                let prev = self.tenv.insert(*l, ty);
                let r = self.cgen(*fb)?;
                let res = self.bind1(*l, &self.tenv[&l], r);
                if let Some(p) = prev {
                    self.tenv.insert(*l, p);
                } else {
                    self.tenv.remove(l);
                }
                Some(res)
            }
            FuncBody::LetCont(k, tyds, def, bod) => {
                let mut prevs = vec![];
                for tyd in *tyds {
                    prevs.push((tyd.ident, self.tenv.insert(tyd.ident, tyd.reft)));
                }
                let prevk = self.kenv.insert(*k, tyds);
                let c1 = self.cgen(*def)?;

                for (idn, reft) in prevs {
                    if let Some(r) = reft {
                        self.tenv.insert(idn, r);
                    } else {
                        self.tenv.remove(&idn);
                    }
                }

                let c2 = self.cgen(*bod)?;
                let res = self.bind(
                    &self.kenv[&k],
                    self.cgen_arena.intern(Constraint::Conj(c1, c2)),
                );

                if let Some(pk) = prevk {
                    self.kenv.insert(*k, pk);
                } else {
                    self.kenv.remove(&k);
                }

                Some(res)
            }
            FuncBody::Call(f, args, k) => {
                let fty = self.tenv.get(&f)?;

                if let Type::Fn { args: tyds, ret } = fty {
                    let kty = self.kenv.get(&k)?;

                    // This continuation can only take one arg.
                    if kty.len() != 1 {
                        return None;
                    }

                    let idents = tyds.iter().map(|x| x.ident).collect::<Vec<_>>();
                    let mut res = self.always;
                    let subst = Subst::new(&idents, &args);

                    for (arg, tyd) in args.iter().zip(tyds.iter()) {
                        let t = self.synth(
                            &self.tenv,
                            RValue::Op(Operand::from_local(self.cps_arena, *arg)),
                        )?;
                        let r =
                            self.subtype(t.into(), tyd.reft.defer_subst(self.cps_arena, &subst))?;

                        res = self.cgen_arena.intern(Constraint::Conj(r, res));
                    }

                    let c = self.subtype(
                        ret.reft.defer_subst(self.cps_arena, &subst),
                        kty[0].reft.into(),
                    )?;

                    Some(self.cgen_arena.intern(Constraint::Conj(c, res)))
                } else {
                    None
                }
            }
            FuncBody::Jump(k, args) => {
                let tyds = self.kenv.get(&k)?;

                let idents = tyds.iter().map(|x| x.ident).collect::<Vec<_>>();
                let mut res = self.always;

                for (arg, tyd) in args.iter().zip(tyds.iter()) {
                    let t = self.synth(
                        &self.tenv,
                        RValue::Op(Operand::from_local(self.cps_arena, *arg)),
                    )?;
                    let s = Subst::new(&idents, &args);
                    let r = self.subtype(t.into(), tyd.reft.defer_subst(self.cps_arena, &s))?;

                    res = self.cgen_arena.intern(Constraint::Conj(r, res));
                }

                Some(res)
            }
            FuncBody::Ite(p, t, e) => {
                let bp = self.cps_arena.preds.intern(Pred::Op(Operand::Path(*p)));
                let c1 = self
                    .cgen_arena
                    .intern(Constraint::Implies(bp, self.cgen(*t)?));
                let c2 = self.cgen_arena.intern(Constraint::Implies(
                    self.cps_arena.preds.intern(Pred::Unary(PredUnOp::Not, bp)),
                    self.cgen(*e)?,
                ));
                Some(self.cgen_arena.intern(Constraint::Conj(c1, c2)))
            }
            FuncBody::Abort => Some(self.always),
        }
    }
}
