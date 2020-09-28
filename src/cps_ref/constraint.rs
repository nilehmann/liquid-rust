use std::collections::HashMap;

use super::{ast::*, subst::ApplySubst, subst::DeferredSubst, subst::Subst};
#[derive(Debug)]
pub enum Constraint<'lr> {
    Subtype(
        BasicType,
        DeferredSubst<Pred<'lr>>,
        DeferredSubst<Pred<'lr>>,
    ),
    Conj(Vec<Constraint<'lr>>),
    Binding {
        bind: Var,
        typ: DeferredSubst<Ty<'lr>>,
        body: Box<Constraint<'lr>>,
    },
    Guard(Pred<'lr>, Box<Constraint<'lr>>),
    True,
}

impl<'lr> Constraint<'lr> {
    pub fn from_bindings<'a, I>(bindings: I, mut body: Constraint<'lr>) -> Constraint<'lr>
    where
        I: DoubleEndedIterator<Item = &'a (Location, Ty<'lr>)>,
        'lr: 'a,
    {
        for (bind, typ) in bindings.rev() {
            body = Constraint::Binding {
                bind: (*bind).into(),
                typ: DeferredSubst::empty(*typ),
                body: box body,
            }
        }
        body
    }
}

#[derive(Debug)]
pub enum ConstraintP {
    Pred(PredC),
    Conj(Vec<ConstraintP>),
    Forall {
        bind: Symbol,
        ty: BasicType,
        hyp: PredC,
        body: Box<ConstraintP>,
    },
    Guard(PredC, Box<ConstraintP>),
    True,
}

impl<'a> From<Constraint<'a>> for ConstraintP {
    fn from(c: Constraint<'a>) -> Self {
        match c {
            Constraint::Subtype(ty, lhs, rhs) => ConstraintP::Forall {
                bind: Symbol::intern("_v"),
                ty,
                hyp: lhs.apply(),
                body: box ConstraintP::Pred(rhs.apply()),
            },
            Constraint::Conj(cs) => ConstraintP::Conj(cs.into_iter().map(|c| c.into()).collect()),
            Constraint::Binding { bind, typ, body } => {
                Embedder::embed(bind, typ).into_iter().rev().fold(
                    ConstraintP::from(*body),
                    |body, (bind, ty, hyp)| ConstraintP::Forall {
                        bind,
                        ty,
                        hyp,
                        body: box body,
                    },
                )
            }
            Constraint::Guard(pred, body) => ConstraintP::Guard(pred.into(), box (*body).into()),
            Constraint::True => ConstraintP::True,
        }
    }
}

#[derive(Debug)]
pub enum PredC {
    Var(Symbol),
    Constant(Constant),
    BinaryOp(BinOp, Box<PredC>, Box<PredC>),
    UnaryOp(UnOp, Box<PredC>),
}

impl<'a> ApplySubst<PredC> for Pred<'a> {
    fn apply(&self, subst: &Subst) -> PredC {
        match self {
            PredS::Constant(c) => PredC::Constant(*c),
            PredS::Place { var, projection } => PredC::Var(place_to_symbol(*var, projection)),
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
        self.collect_field_map(&vec![]);
        self.embed_(&mut vec![])
    }

    fn embed_(&self, projection: &mut Vec<u32>) -> Vec<(Symbol, BasicType, PredC)> {
        match self.typ {
            TyS::Refine { pred, ty } => vec![(
                place_to_symbol(self.var, projection.iter()),
                *ty,
                self.build_pred(pred, &projection),
            )],
            TyS::Tuple(fields) => {
                let mut v = vec![];
                for i in 0..fields.len() {
                    projection.push(i as u32);
                    v.extend(self.embed_(projection));
                    projection.pop();
                }
                v
            }
            _ => vec![],
        }
    }

    fn collect_field_map(&mut self, projection: &Vec<u32>) {
        match self.typ {
            TyS::Tuple(fields) => {
                for (i, (f, _)) in fields.iter().enumerate() {
                    let mut clone = projection.clone();
                    clone.push(i as u32);
                    self.collect_field_map(&clone);
                    self.field_map.insert(*f, clone);
                }
            }
            _ => {}
        }
    }

    fn build_pred(&self, pred: Pred, projection: &[u32]) -> PredC {
        match pred {
            PredS::Constant(c) => PredC::Constant(*c),
            PredS::Place { var, projection } => {
                let mut x = *var;
                if let Some(y) = self.subst.get(x) {
                    x = y;
                }

                let v = match x {
                    Var::Nu => place_to_symbol(self.var, projection),
                    Var::Location(l) => place_to_symbol(l.into(), projection),
                    Var::Field(f) => {
                        place_to_symbol(self.var, self.field_map[&f].iter().chain(projection))
                    }
                };
                PredC::Var(v)
            }
            PredS::BinaryOp(op, lhs, rhs) => PredC::BinaryOp(
                *op,
                box self.build_pred(lhs, projection),
                box self.build_pred(rhs, projection),
            ),
            PredS::UnaryOp(op, p) => PredC::UnaryOp(*op, box self.build_pred(p, projection)),
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
