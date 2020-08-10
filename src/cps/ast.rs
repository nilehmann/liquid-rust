//! This module defines and includes utilities for dealing with the intermediate CPS
//! representation of Rust used by Liquid Rust.

pub use rustc_span::Symbol;

use std::fmt;

/// Each function in MIR is translated to a CpsFn
#[derive(Debug)]
pub struct FnDef {
    pub name: ContIdent,
    pub args: Vec<Tydent>,
    pub cont: ContIdent,
    pub ret: Tydent,
    pub body: Box<FuncBody>,
}

/// A Local is an identifier for some local variable (a fn arg or a let-bound
/// variable)
/// For now, these are symbols, but we could theoretically just use u32s
/// (since the name of the variables doesn't really matter)
pub type Local = Symbol;
pub type ContIdent = Symbol;

/// A Tydent is a Type with an associated identifier.
#[derive(Debug, Clone)]
pub struct Tydent {
    pub ident: Local,
    pub reft: Type,
}

/// A Literal is a boolean or integer literal.
#[derive(Debug, Copy, Clone)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Bool(b) => write!(f, "{}", b),
            Literal::Int(i)  => write!(f, "{}", i),
        }
    }
}

/// A Projection is just a number.
pub type Projection = usize;

/// Paths are local variables with some projections into them.
#[derive(Debug, Clone)]
pub struct Path {
    pub ident: Local,
    pub projs: Vec<Projection>,
}

impl Path {
    /// Substitute all occurrences of symbol `from` with symbol `to` in this path
    pub fn subst(&self, from: Local, to: Local) -> Path {
        if self.ident == from {
            Path {
                ident: to,
                projs: self.projs.clone(),
            }
        } else {
            self.clone()
        }
    }

    pub fn subst_path(&self, from: Local, to: Path) -> Path {
        if self.ident == from {
            let mut new = to;
            new.projs.extend(self.projs.iter());
            new
        } else {
            self.clone()
        }
    }
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ident)?;
        for p in &self.projs {
            write!(f, ".{}", p)?;
        }

        Ok(())
    }
}

impl From<Local> for Path {
    fn from(ident: Local) -> Path {
        Path {
            ident,
            projs: vec![],
        }
    }
}

/// An Operand is either a path or a literal.
#[derive(Debug, Clone)]
pub enum Operand {
    Path(Path),
    Lit(Literal),
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Path(p) => p.fmt(f),
            Operand::Lit(l)  => l.fmt(f),
        }
    }
}

impl Operand {
    /// Substitute all occurrences of symbols in `from` with their respective symbol in `to` in this operand
    pub fn subst(&self, from: &[Local], to: &[Local]) -> Operand {
        match self {
            Operand::Path(og) => {
                let ps = if let Some((f, t)) = from.iter().zip(to.iter()).find(|x| *x.0 == og.ident)
                {
                    og.subst(*f, *t)
                } else {
                    og.clone()
                };
                Operand::Path(ps)
            }
            Operand::Lit(l) => Operand::Lit(*l),
        }
    }

    pub fn subst_path(&self, from: &[Local], to: &[Path]) -> Operand {
        match self {
            Operand::Path(og) => {
                let ps = if let Some((f, t)) = from.iter().zip(to.iter()).find(|x| *x.0 == og.ident)
                {
                    og.subst_path(*f, t.clone())
                } else {
                    og.clone()
                };
                Operand::Path(ps)
            }
            Operand::Lit(l) => Operand::Lit(*l),
        }
    }
}

impl From<Local> for Operand {
    fn from(ident: Local) -> Operand {
        Operand::Path(ident.into())
    }
}

/// An RValue is an operand or some operations on them.
#[derive(Debug)]
pub enum RValue {
    Op(Operand),
    Binary(RBinOp, Operand, Operand),
}

/// BinOpKind is a binary operation on Operands.
#[derive(Debug, Copy, Clone)]
pub enum RBinOp {
    CheckedAdd,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

/// A Body is (a part of) a function body.
#[derive(Debug)]
pub enum FuncBody {
    Let(Local, RValue, Box<FuncBody>),
    LetCont(ContIdent, Vec<Tydent>, Box<FuncBody>, Box<FuncBody>),
    Ite(Path, Box<FuncBody>, Box<FuncBody>),
    Call(Local, Vec<Path>, ContIdent),
    Jump(ContIdent, Vec<Path>),
    Abort,
}

/// A BasicType is a primitive type in the CPS IR; there are bools and ints.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub enum BasicType {
    Bool,
    Int(IntTy),
}

impl BasicType {
    pub fn assignable_to(&self, other: BasicType) -> bool {
        match (self, other) {
            (BasicType::Bool, BasicType::Bool) => true,
            // TODO: we assume all int types are compatible
            (BasicType::Int(_), BasicType::Int(_)) => true,
            _ => false,
        }
    }
}

impl fmt::Display for BasicType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            BasicType::Bool => "Bool",
            BasicType::Int(_) => "Int",
        })?;

        Ok(())
    }
}

// An IntTy is a width and signedness for an int.
#[derive(Debug, PartialEq, Eq, Copy, Clone, Ord, PartialOrd)]
pub enum IntTy {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone)]
pub enum Type {
    Reft {
        ident: Local,
        ty: BasicType,
        pred: Pred,
    },
    Fn {
        args: Vec<Tydent>,
        ret: Box<Tydent>,
    },
    Prod(Vec<Tydent>),
}

impl From<BasicType> for Type {
    fn from(b: BasicType) -> Type {
        Type::Reft {
            ident: Local::intern("_v"),
            ty: b,
            pred: Pred::Op(Operand::Lit(Literal::Bool(true))),
        }
    }
}

impl Type {
    /// Substitute symbols with others in all of this type
    pub fn subst(&self, from: &[Local], to: &[Local]) -> Type {
        match self {
            Type::Reft { ident, ty, pred } => Type::Reft {
                ident: *ident,
                ty: *ty,
                pred: pred.subst(from, to),
            },
            _ => todo!(),
        }
    }

    pub fn subst_path(&self, from: &[Local], to: &[Path]) -> Type {
        match self {
            Type::Reft { ident, ty, pred } => Type::Reft {
                ident: *ident,
                ty: *ty,
                pred: pred.subst_path(from, to),
            },
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Pred {
    Op(Operand),
    Unary(PredUnOp, Box<Pred>),
    Binary(PredBinOp, Box<Pred>, Box<Pred>),
}

impl Pred {
    /// Substitute all occurrences of symbols in `from` with their respective symbol in `to` in this predicate
    pub fn subst(&self, from: &[Local], to: &[Local]) -> Pred {
        match self {
            Pred::Op(op) => Pred::Op(op.subst(from, to)),
            Pred::Unary(un, op) => Pred::Unary(*un, Box::new(op.subst(from, to))),
            Pred::Binary(bin, o1, o2) => Pred::Binary(
                *bin,
                Box::new(o1.subst(from, to)),
                Box::new(o2.subst(from, to)),
            ),
        }
    }

    pub fn subst_path(&self, from: &[Local], to: &[Path]) -> Pred {
        match self {
            Pred::Op(op) => Pred::Op(op.subst_path(from, to)),
            Pred::Unary(un, op) => Pred::Unary(*un, Box::new(op.subst_path(from, to))),
            Pred::Binary(bin, o1, o2) => Pred::Binary(
                *bin,
                Box::new(o1.subst_path(from, to)),
                Box::new(o2.subst_path(from, to)),
            ),
        }
    }
}

impl From<Operand> for Box<Pred> {
    fn from(op: Operand) -> Box<Pred> {
        Box::new(Pred::Op(op))
    }
}

impl From<Local> for Pred {
    fn from(ident: Local) -> Pred {
        Pred::Op(ident.into())
    }
}

impl From<Local> for Box<Pred> {
    fn from(ident: Local) -> Box<Pred> {
        Box::new(Pred::Op(ident.into()))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum PredUnOp {
    Not,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum PredBinOp {
    Add,
    And,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

impl fmt::Display for PredBinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            PredBinOp::Add => "+",
            PredBinOp::And => "&&",
            PredBinOp::Lt => "<",
            PredBinOp::Le => "<=",
            PredBinOp::Eq => "<=",
            PredBinOp::Ge => ">=",
            PredBinOp::Gt => ">",
        })?;

        Ok(())
    }
}

impl From<RBinOp> for PredBinOp {
    fn from(r: RBinOp) -> PredBinOp {
        match r {
            RBinOp::CheckedAdd => PredBinOp::Add,
            RBinOp::Lt => PredBinOp::Lt,
            RBinOp::Le => PredBinOp::Le,
            RBinOp::Eq => PredBinOp::Eq,
            RBinOp::Ge => PredBinOp::Ge,
            RBinOp::Gt => PredBinOp::Gt,
        }
    }
}
