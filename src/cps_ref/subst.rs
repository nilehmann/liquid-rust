use std::{collections::HashMap, hash::Hash, rc::Rc};

use super::ast::Var;

#[derive(Debug, Clone)]
pub struct Subst(Rc<SubstKind>);

#[derive(Debug, Clone)]
enum SubstKind {
    Extend(HashMap<Var, Var>, Rc<SubstKind>),
    Empty,
}

impl SubstKind {
    fn iter<'a>(&'a self) -> SubstIter<'a> {
        SubstIter(self)
    }
}

struct SubstIter<'a>(&'a SubstKind);

impl<'a> Iterator for SubstIter<'a> {
    type Item = &'a HashMap<Var, Var>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            SubstKind::Extend(map, next) => {
                self.0 = next;
                Some(map)
            }
            SubstKind::Empty => None,
        }
    }
}

impl Subst {
    pub fn new(m: HashMap<Var, Var>) -> Self {
        Self::empty().extend(m)
    }

    pub fn empty() -> Self {
        Subst(Rc::new(SubstKind::Empty))
    }

    pub fn get(&self, x: Var) -> Option<Var> {
        for map in self.0.iter() {
            if let Some(y) = map.get(&x) {
                return Some(*y);
            }
        }
        None
    }

    fn extend<I, T>(&self, iter: I) -> Self
    where
        I: IntoIterator<Item = (T, T)>,
        T: Into<Var>,
    {
        Self(Rc::new(SubstKind::Extend(
            iter.into_iter()
                .map(|(x, y)| (x.into(), y.into()))
                .collect(),
            self.0.clone(),
        )))
    }

    pub fn extend2<I1, I2, T>(&self, iter1: I1, iter2: I2) -> Self
    where
        I1: IntoIterator<Item = T>,
        I2: IntoIterator<Item = T>,
        T: Into<Var>,
    {
        self.extend(iter1.into_iter().zip(iter2))
    }
}

#[derive(Debug)]
pub struct DeferredSubst<T>(Subst, T);

impl<'a, K, V> DeferredSubst<HashMap<K, V>>
where
    K: Eq + Hash,
    V: Copy,
{
    pub fn get(&self, k: &K) -> DeferredSubst<V> {
        DeferredSubst(self.0.clone(), self.1[k])
    }
}

impl<T> DeferredSubst<T> {
    pub fn new(subst: Subst, x: T) -> Self {
        DeferredSubst(subst, x)
    }

    pub fn empty(x: T) -> Self {
        DeferredSubst(Subst::empty(), x)
    }

    pub fn split(self) -> (Subst, T) {
        (self.0, self.1)
    }
}

impl<T> DeferredSubst<T> {
    pub fn apply<S>(self) -> S
    where
        T: ApplySubst<S>,
    {
        let (subst, x) = self.split();
        x.apply(&subst)
    }
}

pub trait ApplySubst<T> {
    fn apply(&self, subst: &Subst) -> T;
}
