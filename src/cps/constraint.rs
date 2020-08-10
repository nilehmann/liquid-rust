use super::ast::*;

use std::collections::HashMap;

#[derive(Debug)]
pub enum Constraint {
    Pred(Pred),
    Conj(Box<Constraint>, Box<Constraint>),
    Forall {
        ident: Symbol,
        ty: BasicType,
        hyp: Pred,
        con: Box<Constraint>,
    },
    Implies(Box<Pred>, Box<Constraint>),
}

impl Constraint {
    pub fn always() -> Constraint {
        Constraint::Pred(Pred::Op(Operand::Lit(Literal::Bool(true))))
    }
}

fn bind1(name: Local, ty: &Type, rest: Constraint) -> Constraint {
    let mut res = rest;

    match ty {
        Type::Reft { ident, ty, pred } => {
            res = Constraint::Forall {
                ident: name,
                ty: *ty,
                hyp: pred.subst(&[*ident], &[name]),
                con: Box::new(res),
            };
        }
        Type::Prod(ptys) => {
            res = bind(&ptys, res);
        }
        _ => {}
    }

    res
}

/// Sometimes, we want to create an implication constraint where the hypothesis is
/// "we have variables x_i of type T_i", where T_i is some refinement type, and the
/// conclusion can mention these variables. A Forall constraint allows us to bind
/// these variables in the hypothesis so that the conclusion can use them, but
/// a Forall constraint only keeps track of the BasicType of a variable; naively
/// constructing a Forall Constraint would throw away our predicates.
///
/// bind creates Forall Constraints such that refinements over Refts are preserved.
fn bind(tyds: &[Tydent], rest: Constraint) -> Constraint {
    let mut res = rest;

    for tyd in tyds.iter().rev() {
        res = bind1(tyd.ident, &tyd.reft, res);
    }

    res
}

/// Produces a subtyping constraint, where the constraint is such that
/// the first type is a subtype of the second.
///
/// If no valid constraint could be produced, returns None
fn subtype(a: Type, b: Type) -> Option<Constraint> {
    match (a, b) {
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
            if ba.assignable_to(bb) {
                Some(Constraint::Forall {
                    ident: ia,
                    ty: ba,
                    hyp: pa,
                    con: Box::new(Constraint::Pred(pb.subst(&[ib], &[ia]))),
                })
            } else {
                None
            }
        }
        (Type::Fn { args: a1s, ret: r1 }, Type::Fn { args: a2s, ret: r2 }) => {
            // We first create a constraint on the return types of the fns
            let a1is = a1s.iter().map(|x| x.ident).collect::<Vec<Symbol>>();
            let a2is = a2s.iter().map(|x| x.ident).collect::<Vec<Symbol>>();

            let ret_constr = subtype((*r1).reft.subst(&a1is, &a2is), (*r2).reft)?;

            let res: Option<Constraint> =
                a1s.into_iter()
                    .zip(a2s.into_iter())
                    .rev()
                    .try_fold(ret_constr, |acc, (a1, a2)| {
                        let sub = subtype(a2.reft.clone(), a1.reft.subst(&a1is, &a2is))?;
                        Some(bind(&[a2], Constraint::Conj(Box::new(acc), Box::new(sub))))
                    });

            res
        }
        _ => None,
    }
}

/// A typing environment is a map from names to types
pub type TEnv = HashMap<Local, Type>;

/// A continuation environment is a map from names to lists of args
pub type KEnv = HashMap<Local, Vec<Tydent>>;

pub fn synth(tenv: &TEnv, rval: RValue) -> Option<Type> {
    match rval {
        RValue::Op(Operand::Lit(l)) => {
            let v = Local::intern("_v");
            let res = Type::Reft {
                ident: v,
                ty: match l {
                    Literal::Bool(_) => BasicType::Bool,
                    Literal::Int(_) => BasicType::Int(IntTy::I32),
                },
                pred: Pred::Binary(PredBinOp::Eq, v.into(), Operand::Lit(l).into()),
            };

            Some(res)
        }
        RValue::Op(Operand::Path(p)) => {
            let mut ty = tenv.get(&p.ident)?;

            for proj in p.projs {
                if let Type::Prod(ts) = ty {
                    ty = &ts.get(proj)?.reft;
                } else {
                    return None;
                }
            }

            Some(ty.clone())
        }
        RValue::Binary(RBinOp::CheckedAdd, o1, o2) => {
            let loc = Local::intern("_v");
            let tyd1 = Tydent {
                ident: loc,
                reft: Type::Reft {
                    ident: loc,
                    // TODO: proper int type recognition
                    ty: BasicType::Int(IntTy::I128),
                    pred: Pred::Binary(
                        PredBinOp::Eq,
                        Box::new(loc.into()),
                        Box::new(Pred::Binary(PredBinOp::Add, o1.into(), o2.into())),
                    ),
                },
            };
            let tyd2 = Tydent {
                ident: Local::intern("_w"),
                reft: BasicType::Bool.into(),
            };
            Some(Type::Prod(vec![tyd1, tyd2]))
        }
        RValue::Binary(cmp, o1, o2) => {
            let loc = Local::intern("_v");
            let tyd1 = Tydent {
                ident: loc,
                reft: Type::Reft {
                    ident: loc,
                    ty: BasicType::Bool,
                    pred: Pred::Binary(
                        PredBinOp::Eq,
                        Box::new(loc.into()),
                        Box::new(Pred::Binary(cmp.into(), o1.into(), o2.into())),
                    ),
                },
            };
            let tyd2 = Tydent {
                ident: Local::intern("_w"),
                reft: BasicType::Bool.into(),
            };
            Some(Type::Prod(vec![tyd1, tyd2]))
        }
    }
}

pub struct ConstraintGen {
    tenv: TEnv,
    kenv: KEnv,
}

impl ConstraintGen {
    pub fn new() -> Self {
        ConstraintGen {
            tenv: HashMap::new(),
            kenv: HashMap::new(),
        }
    }

    pub fn check_fns(&mut self, fs: Vec<FnDef>) -> Option<Vec<Constraint>> {
        // For each function we have, we check it, then add its type
        // to our environment
        let mut cons = vec![];

        for f in fs {
            let args = f.args.clone();
            let ret = Box::new(f.ret.clone());
            let name = f.name;
            cons.push(self.check_fn(f)?);
            self.tenv.insert(name, Type::Fn { args, ret });
        }

        Some(cons)
    }

    pub fn check_fn(&mut self, f: FnDef) -> Option<Constraint> {
        // We first add all the arguments of the function to the TEnv.
        let mut prevs = vec![];
        for arg in f.args {
            prevs.push((arg.ident, self.tenv.insert(arg.ident, arg.reft)));
        }

        // We then add the result cont to the environment
        let prevk = self.kenv.insert(f.cont, vec![f.ret]);

        // Actually do codegen for this fn
        let res = self.cgen(*f.body);

        // Finally, remove what we added to the env, replacing them with
        // their prev values if needed.
        if let Some(pk) = prevk {
            self.kenv.insert(f.cont, pk);
        } else {
            self.kenv.remove(&f.cont);
        }

        for (idn, reft) in prevs {
            if let Some(r) = reft {
                self.tenv.insert(idn, r);
            } else {
                self.tenv.remove(&idn);
            }
        }

        res        
    }

    pub fn cgen(&mut self, body: FuncBody) -> Option<Constraint> {
        match body {
            FuncBody::Let(l, rv, fb) => {
                let ty = synth(&self.tenv, rv)?;
                let prev = self.tenv.insert(l, ty);
                let r = self.cgen(*fb)?;
                let res = bind1(l, &self.tenv[&l], r);
                if let Some(p) = prev {
                    self.tenv.insert(l, p);
                } else {
                    self.tenv.remove(&l);
                }
                Some(res)
            }
            FuncBody::LetCont(k, tyds, def, bod) => {
                let mut prevs = vec![];
                for tyd in &tyds {
                    prevs.push((tyd.ident, self.tenv.insert(tyd.ident, tyd.reft.clone())));
                }
                let prevk = self.kenv.insert(k, tyds);
                let c1 = self.cgen(*def)?;

                for (idn, reft) in prevs {
                    if let Some(r) = reft {
                        self.tenv.insert(idn, r);
                    } else {
                        self.tenv.remove(&idn);
                    }
                }

                let c2 = self.cgen(*bod)?;
                let res = bind(&self.kenv[&k], Constraint::Conj(Box::new(c1), Box::new(c2)));

                if let Some(pk) = prevk {
                    self.kenv.insert(k, pk);
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
                    let mut res = Constraint::always();

                    for (arg, tyd) in args.iter().zip(tyds.iter()) {
                        let t = synth(&self.tenv, RValue::Op(Operand::Path(arg.clone())))?;
                        let r = subtype(t, tyd.reft.subst_path(&idents, &args))?;

                        res = Constraint::Conj(Box::new(r), Box::new(res));
                    }

                    let c = subtype(ret.reft.subst_path(&idents, &args), kty[0].reft.clone())?;

                    Some(Constraint::Conj(Box::new(c), Box::new(res)))
                } else {
                    None
                }
            }
            FuncBody::Jump(k, args) => {
                let tyds = self.kenv.get(&k)?;

                let idents = tyds.iter().map(|x| x.ident).collect::<Vec<_>>();
                let mut res = Constraint::always();

                for (arg, tyd) in args.iter().zip(tyds.iter()) {
                    let t = synth(&self.tenv, RValue::Op(Operand::Path(arg.clone())))?;
                    // TODO: substitution is a little broke; problem:
                    // {x: i32 | x >= 0}[y.0/x] => {x: i32 | y.0 >= 0}
                    let r = subtype(t, tyd.reft.subst_path(&idents, &args))?;

                    res = Constraint::Conj(Box::new(r), Box::new(res));
                }


                Some(res)
            }
            FuncBody::Ite(p, t, e) => {
                let bp = Box::new(Pred::Op(Operand::Path(p)));
                let c1 = Constraint::Implies(bp.clone(), Box::new(self.cgen(*t)?));
                let c2 = Constraint::Implies(
                    Box::new(Pred::Unary(PredUnOp::Not, bp)),
                    Box::new(self.cgen(*e)?),
                );
                Some(Constraint::Conj(Box::new(c1), Box::new(c2)))
            }
            FuncBody::Abort => Some(Constraint::always()),
        }
    }
}
