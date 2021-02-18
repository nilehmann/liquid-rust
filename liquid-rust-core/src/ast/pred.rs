use std::fmt;

use super::BaseTy;
use crate::names::{Field, Location};

#[derive(Clone)]
pub enum Pred {
    Constant(Constant),
    Place(Place),
    BinaryOp(BinOp, Box<Pred>, Box<Pred>),
    UnaryOp(UnOp, Box<Pred>),
}

impl Pred {
    pub fn tt() -> Self {
        Self::Constant(Constant::Bool(true))
    }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum Constant {
    Bool(bool),
    Int(u128),
    Unit,
}

impl Constant {
    pub fn base_ty(&self) -> BaseTy {
        match self {
            Constant::Bool(_) => BaseTy::Bool,
            Constant::Int(_) => BaseTy::Int,
            Constant::Unit => BaseTy::Unit,
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Int(n) => write!(f, "{}", n),
            Constant::Unit => write!(f, "()"),
        }
    }
}

#[derive(Eq, PartialEq, Clone, Hash)]
pub struct Place {
    pub base: Var,
    pub projs: Vec<usize>,
}

impl Place {
    pub fn extend_path(&self, n: usize) -> Self {
        let mut projs = self.projs.clone();
        projs.push(n);
        Place {
            base: self.base,
            projs,
        }
    }
}

impl<T> From<T> for Place
where
    T: Into<Var>,
{
    fn from(base: T) -> Self {
        Place {
            base: base.into(),
            projs: Vec::new(),
        }
    }
}

#[derive(PartialEq, Eq, Copy, Clone, Debug, Hash)]
pub enum Var {
    Nu,
    Location(Location),
    Field(Field),
}

impl From<Location> for Var {
    fn from(v: Location) -> Self {
        Var::Location(v)
    }
}

impl From<Field> for Var {
    fn from(v: Field) -> Self {
        Var::Field(v)
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Var::Nu => write!(f, "V"),
            Var::Location(l) => write!(f, "{}", l),
            Var::Field(fld) => write!(f, "{}", fld),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum BinOp {
    Iff,
    And,
    Or,

    Add,
    Sub,

    Eq,
    Neq,
    Lt,
    Gt,
    Le,
    Ge,
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Iff => write!(f, "<=>"),
            BinOp::And => write!(f, "&&"),
            BinOp::Or => write!(f, "||"),

            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),

            BinOp::Eq => write!(f, "="),
            BinOp::Neq => write!(f, "!="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Gt => write!(f, ">"),
            BinOp::Le => write!(f, "<="),
            BinOp::Ge => write!(f, ">="),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Not => write!(f, "!"),
            UnOp::Neg => write!(f, "-"),
        }
    }
}
