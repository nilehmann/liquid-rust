//! This module defines and includes utilities for dealing with the intermediate CPS
//! representation of Rust used by Liquid Rust.

use crate::context::ArenaInterner;

use rustc_arena::TypedArena;
use rustc_span::Span;
pub use rustc_span::Symbol;

use std::fmt;

// This is for LALRPOP :/
pub type Slice<T> = [T];

pub struct CpsArena<'cx> {
    pub preds: ArenaInterner<'cx, Pred<'cx>>,
    pub refts: ArenaInterner<'cx, Type<'cx>>,
    pub bodies: ArenaInterner<'cx, FuncBody<'cx>>,
    pub substs: ArenaInterner<'cx, SubstNode<'cx>>,

    // TODO: use ArenaInterner.alloc_slice/alloc_from_iter?
    pub tyd_args: TypedArena<Vec<Tydent<'cx>>>,
    pub loc_args: TypedArena<Vec<Local>>,
    pub projs: TypedArena<Vec<Projection>>,
}

impl CpsArena<'_> {
    pub fn new() -> Self {
        let preds = ArenaInterner::new(TypedArena::default());
        let refts = ArenaInterner::new(TypedArena::default());
        let bodies = ArenaInterner::new(TypedArena::default());
        let substs = ArenaInterner::new(TypedArena::default());

        let tyd_args = TypedArena::default();
        let loc_args = TypedArena::default();
        let projs = TypedArena::default();

        CpsArena {
            preds,
            refts,
            bodies,
            substs,
            tyd_args,
            loc_args,
            projs,
        }
    }
}

pub struct Subst<'a> {
    from: &'a [Local],
    to: &'a [Local],
}

impl<'a> Subst<'a> {
    pub fn new(from: &'a [Local], to: &'a [Local]) -> Self {
        Subst { from, to }
    }

    pub fn empty() -> Self {
        Subst { from: &[], to: &[] }
    }

    pub fn get(&self, l: &Local) -> Option<&Local> {
        for (f, t) in self.from.iter().zip(self.to.iter()) {
            if *l == *f {
                return Some(t);
            }
        }

        None
    }
}

/// A DeferSubst is a singly linked list of symbol subtitutions.
/// It contains a pointer to the last element of the list,
/// or None of the last element is empty.
/// We do things this way to facilitate sharing of substitutions across multiple
/// types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeferSubst<'cx>(Option<&'cx SubstNode<'cx>>);

impl<'cx> DeferSubst<'cx> {
    pub fn new(arena: &'cx CpsArena<'cx>, fs: &[Local], ts: &[Local]) -> DeferSubst<'cx> {
        DeferSubst(SubstNode::add_substs(arena, None, fs, ts))
    }

    pub fn push(self, arena: &'cx CpsArena<'cx>, fs: &[Local], ts: &[Local]) -> DeferSubst<'cx> {
        DeferSubst(SubstNode::add_substs(arena, self.0, fs, ts))
    }

    pub fn collect(&self) -> (Vec<Local>, Vec<Local>) {
        let mut fs = Vec::new();
        let mut ts = Vec::new();

        let mut last = self.0;

        while let Some(n) = last {
            fs.push(n.from);
            ts.push(n.to);

            last = n.prev;
        }

        (fs, ts)
    }

    pub fn get(&self, l: &Local) -> Option<Local> {
        self.0.and_then(|n| n.get(l))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SubstNode<'cx> {
    prev: Option<&'cx SubstNode<'cx>>,
    from: Local,
    to: Local,
}

impl<'cx> SubstNode<'cx> {
    fn add_substs(
        arena: &'cx CpsArena<'cx>,
        prev: Option<&'cx SubstNode<'cx>>,
        fs: &[Local],
        ts: &[Local],
    ) -> Option<&'cx SubstNode<'cx>> {
        let mut res = prev;

        for (f, t) in fs.iter().zip(ts.iter()) {
            res = Some(arena.substs.intern(SubstNode {
                prev: res,
                from: *f,
                to: *t,
            }));
        }

        res
    }

    fn get(&self, l: &Local) -> Option<Local> {
        if self.from == *l {
            Some(self.to)
        } else {
            self.prev.and_then(|p| p.get(l))
        }
    }
}

/// Each function in MIR is translated to a CpsFn
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnDef<'cx> {
    pub name: ContIdent,
    pub args: &'cx [Tydent<'cx>],
    pub cont: ContIdent,
    pub ret: Tydent<'cx>,
    pub body: &'cx FuncBody<'cx>,
    pub span: Span,
}

/// A Local is an identifier for some local variable (a fn arg or a let-bound
/// variable)
/// For now, these are symbols, but we could theoretically just use u32s
/// (since the name of the variables doesn'cx really matter)
pub type Local = Symbol;
pub type ContIdent = Symbol;

/// A Tydent is a Type with an associated identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Tydent<'cx> {
    pub ident: Local,
    pub reft: &'cx Type<'cx>,
}

/// A Literal is a boolean or integer literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Literal {
    Bool(bool),
    Int(i128),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Bool(b) => write!(f, "{}", b),
            Literal::Int(i) => write!(f, "{}", i),
        }
    }
}

/// A Projection is just a number.
pub type Projection = usize;

/// Paths are local variables with some projections into them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Path<'cx> {
    pub ident: Local,
    pub projs: &'cx [Projection],
}

impl<'cx> Path<'cx> {
    /// Substitute all occurrences of symbol `from` with symbol `to` in this path
    pub fn run_subst(&self, subst: &Subst) -> Path {
        Path {
            ident: *subst.get(&self.ident).unwrap_or(&self.ident),
            projs: &self.projs[..],
        }
    }

    pub fn from_local(arena: &'cx CpsArena, ident: Local) -> Path<'cx> {
        Path {
            ident,
            // TODO: intern this somehow
            projs: arena.projs.alloc(vec![]),
        }
    }
}

impl fmt::Display for Path<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ident)?;
        for p in self.projs {
            write!(f, ".{}", p)?;
        }

        Ok(())
    }
}

/// An Operand is either a path or a literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operand<'cx> {
    Path(Path<'cx>),
    Lit(Literal),
}

impl fmt::Display for Operand<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Path(p) => p.fmt(f),
            Operand::Lit(l) => l.fmt(f),
        }
    }
}

impl<'cx> Operand<'cx> {
    /// Substitute all occurrences of symbols in `from` with their respective symbol in `to` in this operand
    pub fn run_subst(&self, subst: &Subst) -> Operand {
        match self {
            Operand::Path(og) => Operand::Path(og.run_subst(subst)),
            Operand::Lit(l) => Operand::Lit(*l),
        }
    }

    pub fn from_local(arena: &'cx CpsArena, ident: Local) -> Operand<'cx> {
        Operand::Path(Path::from_local(arena, ident))
    }
}

/// An RValue is an operand or some operations on them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RValue<'cx> {
    Op(Operand<'cx>),
    Binary(RBinOp, Operand<'cx>, Operand<'cx>),
}

/// BinOpKind is a binary operation on Operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RBinOp {
    CheckedAdd,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

/// A Body is (a part of) a function body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FuncBody<'cx> {
    Let(Local, RValue<'cx>, &'cx FuncBody<'cx>),
    LetCont(
        ContIdent,
        &'cx [Tydent<'cx>],
        &'cx FuncBody<'cx>,
        &'cx FuncBody<'cx>,
    ),
    Ite(Path<'cx>, &'cx FuncBody<'cx>, &'cx FuncBody<'cx>),
    Call(Local, &'cx [Local], ContIdent),
    Jump(ContIdent, &'cx [Local]),
    Abort,
}

/// A BasicType is a primitive type in the CPS IR; there are bools and ints.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
        write!(
            f,
            "{}",
            match self {
                BasicType::Bool => "Bool",
                BasicType::Int(_) => "Int",
            }
        )?;

        Ok(())
    }
}

// An IntTy is a width and signedness for an int.
#[derive(Debug, PartialEq, Eq, Copy, Clone, Ord, PartialOrd, Hash)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Type<'cx> {
    Reft {
        ident: Local,
        ty: BasicType,
        pred: &'cx Pred<'cx>,
    },
    Fn {
        args: &'cx [Tydent<'cx>],
        ret: Tydent<'cx>,
    },
    Prod(&'cx [Tydent<'cx>]),
}

impl<'cx> Type<'cx> {
    /// Substitute symbols with others in all of this type
    pub fn run_subst(&'cx self, arena: &'cx CpsArena<'cx>, subst: &Subst) -> &'cx Type<'cx> {
        match self {
            Type::Reft { ident, ty, pred } => {
                let nid = *subst.get(ident).unwrap_or(ident);
                let pred = pred.run_subst(arena, subst);
                arena.refts.intern(Type::Reft {
                    ident: nid,
                    ty: *ty,
                    pred,
                })
            }
            x => x,
        }
    }

    pub fn as_deferred(&'cx self, subst: DeferSubst<'cx>) -> DeferType<'cx> {
        DeferType { reft: self, subst }
    }

    pub fn defer_subst(&'cx self, arena: &'cx CpsArena<'cx>, subst: &Subst) -> DeferType<'cx> {
        DeferType::new(arena, self, subst)
    }

    pub fn extend_subst(
        &'cx self,
        arena: &'cx CpsArena<'cx>,
        ds: DeferSubst<'cx>,
        subst: &Subst,
    ) -> DeferType<'cx> {
        DeferType {
            reft: self,
            subst: ds.push(arena, subst.from, subst.to),
        }
    }

    pub fn from_basic(arena: &'cx CpsArena<'cx>, b: BasicType) -> &'cx Type<'cx> {
        arena.refts.intern(Type::Reft {
            ident: Local::intern("_v").into(),
            ty: b,
            pred: arena
                .preds
                .intern(Pred::Op(Operand::Lit(Literal::Bool(true)))),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeferType<'cx> {
    pub reft: &'cx Type<'cx>,
    pub subst: DeferSubst<'cx>,
}

impl<'cx> DeferType<'cx> {
    pub fn new(arena: &'cx CpsArena<'cx>, reft: &'cx Type<'cx>, subst: &Subst) -> DeferType<'cx> {
        DeferType {
            reft,
            subst: DeferSubst::new(arena, subst.from, subst.to),
        }
    }

    pub fn empty(reft: &'cx Type<'cx>) -> DeferType<'cx> {
        DeferType {
            reft,
            subst: DeferSubst(None),
        }
    }

    pub fn run_subst(&self, arena: &'cx CpsArena<'cx>) -> &'cx Type<'cx> {
        let (fs, ts) = self.subst.collect();

        self.reft.run_subst(arena, &Subst::new(&fs[..], &ts[..]))
    }
}

impl<'cx> From<&'cx Type<'cx>> for DeferType<'cx> {
    fn from(x: &'cx Type<'cx>) -> DeferType<'cx> {
        DeferType::empty(x)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Pred<'cx> {
    Op(Operand<'cx>),
    Unary(PredUnOp, &'cx Pred<'cx>),
    Binary(PredBinOp, &'cx Pred<'cx>, &'cx Pred<'cx>),
}

impl<'cx> Pred<'cx> {
    /// Substitute all occurrences of symbols in `from` with their respective symbol in `to` in this predicate
    pub fn run_subst(&'cx self, arena: &'cx CpsArena<'cx>, subst: &Subst) -> &'cx Pred<'cx> {
        match self {
            Pred::Op(op) => arena.preds.intern(Pred::Op(op.run_subst(subst))),
            Pred::Unary(un, p) => {
                let new_p = p.run_subst(arena, subst);
                arena.preds.intern(Pred::Unary(*un, new_p))
            }
            Pred::Binary(bin, p1, p2) => {
                let new_p1 = p1.run_subst(arena, subst);
                let new_p2 = p2.run_subst(arena, subst);
                arena.preds.intern(Pred::Binary(*bin, new_p1, new_p2))
            }
        }
    }

    pub fn from_local(arena: &'cx CpsArena<'cx>, l: Local) -> &'cx Pred<'cx> {
        arena.preds.intern(Pred::Op(Operand::from_local(arena, l)))
    }

    pub fn from_op(arena: &'cx CpsArena<'cx>, op: Operand<'cx>) -> &'cx Pred<'cx> {
        arena.preds.intern(Pred::Op(op))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PredUnOp {
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
        write!(
            f,
            "{}",
            match self {
                PredBinOp::Add => "+",
                PredBinOp::And => "&&",
                PredBinOp::Lt => "<",
                PredBinOp::Le => "<=",
                PredBinOp::Eq => "=",
                PredBinOp::Ge => ">=",
                PredBinOp::Gt => ">",
            }
        )?;

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
