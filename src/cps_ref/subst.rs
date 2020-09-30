use std::{collections::HashMap, hash::Hash, ops::Index, rc::Rc};

use super::ast::Var;

#[derive(Debug, Clone)]
pub struct Subst(Rc<HashMap<Var, Var>>);

impl Subst {
    pub fn new(m: HashMap<Var, Var>) -> Self {
        Self(Rc::new(m))
    }

    pub fn empty() -> Self {
        Self(Rc::new(HashMap::new()))
    }

    pub fn get(&self, x: Var) -> Option<Var> {
        self.0.get(&x).copied()
    }

    fn extend<I, T>(&self, iter: I) -> Self
    where
        I: IntoIterator<Item = (T, T)>,
        T: Into<Var>,
    {
        let mut m: HashMap<Var, Var> = iter
            .into_iter()
            .map(|(x, y)| (x.into(), y.into()))
            .collect();
        for (x, y) in self.0.iter() {
            if let Some(z) = m.get(&y).copied() {
                m.insert(*x, z);
            } else {
                m.insert(*x, *y);
            }
        }
        Self(Rc::new(m))
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

#[derive(Debug, Clone)]
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

impl<T> From<T> for DeferredSubst<T> {
    fn from(x: T) -> Self {
        DeferredSubst::empty(x)
    }
}

pub trait ApplySubst<T> {
    fn apply(&self, subst: &Subst) -> T;
}
