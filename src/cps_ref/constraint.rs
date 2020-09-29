use std::{collections::HashMap, fmt::Debug};

use super::{ast::*, subst::ApplySubst, subst::DeferredSubst, subst::Subst};

pub type Bindings<'lr> = Vec<(Location, Ty<'lr>)>;
#[derive(Debug)]
pub enum Constraint {
    Pred(PredC),
    Conj(Vec<Constraint>),
    Forall {
        bind: Symbol,
        ty: BasicType,
        hyp: PredC,
        body: Box<Constraint>,
    },
    Guard(PredC, Box<Constraint>),
    True,
}

pub enum PredC {
    Var(Symbol),
    Constant(Constant),
    BinaryOp(BinOp, Box<PredC>, Box<PredC>),
    UnaryOp(UnOp, Box<PredC>),
}

impl Constraint {
    pub fn from_bindings<'a, I, V, T>(bindings: I, mut body: Constraint) -> Self
    where
        I: DoubleEndedIterator<Item = (V, T)>,
        V: Into<Var>,
        T: Into<DeferredSubst<Ty<'a>>>,
    {
        for (x, typ) in bindings.rev() {
            for (y, ty, hyp) in Embedder::embed(x.into(), typ.into()).into_iter().rev() {
                body = Constraint::Forall {
                    bind: y,
                    ty,
                    hyp,
                    body: box body,
                }
            }
        }
        body
    }

    pub fn from_binding<'a, V, T>(bind: V, typ: T, body: Constraint) -> Self
    where
        V: Into<Var>,
        T: Into<DeferredSubst<Ty<'a>>>,
    {
        Self::from_bindings(vec![(bind, typ)].into_iter(), body)
    }

    pub fn from_subtype<'a>(
        ty: BasicType,
        pred1: DeferredSubst<Pred<'a>>,
        pred2: DeferredSubst<Pred<'a>>,
    ) -> Self {
        Constraint::Forall {
            bind: Symbol::intern(&format!("{:?}", Var::Nu)),
            ty,
            hyp: pred1.apply(),
            body: box Constraint::Pred(pred2.apply()),
        }
    }

    pub fn guard<'a>(pred: impl Into<DeferredSubst<Pred<'a>>>, body: Constraint) -> Self {
        let p: DeferredSubst<Pred> = pred.into();
        Constraint::Guard(p.apply(), box body)
    }
}

impl<'a> ApplySubst<PredC> for Pred<'a> {
    fn apply(&self, subst: &Subst) -> PredC {
        match self {
            PredS::Constant(c) => PredC::Constant(*c),
            PredS::Place { var, projection } => {
                PredC::Var(place_to_symbol(subst.get(*var).unwrap_or(*var), projection))
            }
            PredS::BinaryOp(op, lhs, rhs) => {
                PredC::BinaryOp(*op, box lhs.apply(subst), box rhs.apply(subst))
            }
            PredS::UnaryOp(op, p) => PredC::UnaryOp(*op, box p.apply(subst)),
        }
    }
}

impl<'a> From<Pred<'a>> for PredC {
    fn from(pred: Pred<'a>) -> Self {
        pred.apply(&Subst::empty())
    }
}

struct Embedder<'a> {
    typ: Ty<'a>,
    subst: Subst,
    var: Var,
    field_map: HashMap<Field, Vec<u32>>,
}

impl<'a> Embedder<'a> {
    fn embed(var: Var, typ: DeferredSubst<Ty<'a>>) -> Vec<(Symbol, BasicType, PredC)> {
        let (subst, typ) = typ.split();
        Self {
            typ,
            subst,
            var,
            field_map: HashMap::new(),
        }
        .run()
    }

    fn run(mut self) -> Vec<(Symbol, BasicType, PredC)> {
        self.collect_field_map(self.typ, &vec![]);
        self.embed_(self.typ, &mut vec![])
    }

    fn embed_(&self, typ: Ty<'a>, projection: &mut Vec<u32>) -> Vec<(Symbol, BasicType, PredC)> {
        match typ {
            TyS::Refine { pred, ty } => vec![(
                place_to_symbol(self.var, projection.iter()),
                *ty,
                self.build_pred(pred, &projection),
            )],
            TyS::Tuple(fields) => {
                let mut v = vec![];
                for i in 0..fields.len() {
                    projection.push(i as u32);
                    v.extend(self.embed_(fields[i].1, projection));
                    projection.pop();
                }
                v
            }
            _ => vec![],
        }
    }

    fn collect_field_map(&mut self, typ: Ty<'a>, projection: &Vec<u32>) {
        match typ {
            TyS::Tuple(fields) => {
                for (i, (f, t)) in fields.iter().enumerate() {
                    let mut clone = projection.clone();
                    clone.push(i as u32);
                    self.collect_field_map(t, &clone);
                    self.field_map.insert(*f, clone);
                }
            }
            _ => {}
        }
    }

    fn build_pred(&self, pred: Pred, curr_proj: &[u32]) -> PredC {
        match pred {
            PredS::Constant(c) => PredC::Constant(*c),
            PredS::Place { var, projection } => {
                let mut x = *var;
                if let Some(y) = self.subst.get(x) {
                    x = y;
                }

                let v = match x {
                    Var::Nu => place_to_symbol(self.var, curr_proj.iter().chain(projection)),
                    Var::Location(l) => place_to_symbol(l.into(), projection),
                    Var::Field(f) => {
                        place_to_symbol(self.var, self.field_map[&f].iter().chain(projection))
                    }
                };
                PredC::Var(v)
            }
            PredS::BinaryOp(op, lhs, rhs) => PredC::BinaryOp(
                *op,
                box self.build_pred(lhs, curr_proj),
                box self.build_pred(rhs, curr_proj),
            ),
            PredS::UnaryOp(op, p) => PredC::UnaryOp(*op, box self.build_pred(p, curr_proj)),
        }
    }
}

fn place_to_symbol<'a, I>(var: Var, projection: I) -> Symbol
where
    I: IntoIterator<Item = &'a u32>,
{
    let mut s = format!("{:?}", var);
    for p in projection {
        s.push_str(&format!(".{}", p));
    }
    Symbol::intern(&s)
}

impl Debug for PredC {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredC::Constant(c) => Debug::fmt(&c, f)?,
            PredC::Var(s) => {
                write!(f, "{}", &*s.as_str())?;
            }
            PredC::BinaryOp(op, lhs, rhs) => {
                write!(f, "({:?} {:?} {:?})", lhs, op, rhs)?;
            }
            PredC::UnaryOp(op, operand) => {
                write!(f, "{:?}({:?})", op, operand)?;
            }
        }
        Ok(())
    }
}
