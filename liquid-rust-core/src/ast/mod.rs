pub mod pred;
pub mod visitor;

use std::{collections::HashMap, fmt};

pub use self::pred::Pred;
use crate::names::{ContId, Field, FnId, Local, Location};

#[derive(Default)]
pub struct Program<I> {
    functions: HashMap<FnId, FnDef<I>>,
}

impl<I> Program<I> {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
        }
    }

    pub fn functions(&self) -> impl Iterator<Item = &FnDef<I>> {
        self.functions.iter().map(|(_, def)| def)
    }

    pub fn add_fn(&mut self, fn_id: FnId, def: FnDef<I>) {
        self.functions.insert(fn_id, def);
    }

    pub fn iter(&self) -> impl Iterator<Item = (&FnId, &FnDef<I>)> {
        self.functions.iter()
    }
}

impl<I> IntoIterator for Program<I> {
    type Item = (FnId, FnDef<I>);

    type IntoIter = std::collections::hash_map::IntoIter<FnId, FnDef<I>>;

    fn into_iter(self) -> Self::IntoIter {
        self.functions.into_iter()
    }
}

pub struct FnDef<I> {
    pub name: FnId,
    pub ty: FnDecl,
    pub params: Vec<Local>,
    pub body: FnBody<I>,
    pub ret: ContId,
}

pub enum FnBody<I> {
    LetCont(Vec<ContDef<I>>, Box<FnBody<I>>),
    Ite {
        discr: Place,
        then: Box<FnBody<I>>,
        else_: Box<FnBody<I>>,
    },
    Call {
        func: FnId,
        args: Vec<Local>,
        destination: Option<(Place, ContId)>,
    },
    Jump {
        target: ContId,
        args: Vec<Local>,
    },
    Seq(Statement<I>, Box<FnBody<I>>),
    Abort,
}

pub struct ContDef<I> {
    pub name: ContId,
    pub params: Vec<Local>,
    pub body: Box<FnBody<I>>,
    pub ty: ContTy,
}

pub struct ContTy {
    pub heap: Heap,
    pub locals: Vec<(Local, Location)>,
    pub inputs: Vec<Location>,
}

pub struct Statement<I> {
    pub source_info: I,
    pub kind: StatementKind,
}

pub enum StatementKind {
    Let(Local, TypeLayout),
    Assign(Place, Rvalue),
    Drop(Place),
    Nop,
}

#[derive(Debug)]
pub enum TypeLayout {
    Tuple(Vec<TypeLayout>),
    Block(usize),
}
#[derive(Debug)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Debug)]
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

#[derive(Debug)]
pub enum Rvalue {
    Use(Operand),
    Ref(BorrowKind, Place),
    BinaryOp(BinOp, Operand, Operand),
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum UnOp {
    Not,
    Neg,
}
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum BaseTy {
    Unit,
    Bool,
    Int,
}

impl fmt::Display for BaseTy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BaseTy::Unit => write!(f, "()"),
            BaseTy::Bool => write!(f, "bool"),
            BaseTy::Int => write!(f, "int"),
        }
    }
}

#[derive(Eq, PartialEq, Copy, Clone, Debug, Hash, PartialOrd)]
pub enum BorrowKind {
    Shared,
    Mut,
}

impl BorrowKind {
    pub fn is_mut(self) -> bool {
        matches!(self, BorrowKind::Mut)
    }
}

#[derive(Clone)]
pub enum Ty {
    OwnRef(Location),
    Ref(BorrowKind, Region, Location),
    Tuple(Vec<(Field, Ty)>),
    Uninit(usize),
    Refine(BaseTy, Refine),
}

impl Ty {
    pub fn unit() -> Ty {
        Ty::Refine(
            BaseTy::Unit,
            Refine::Pred(pred::Pred::Constant(pred::Constant::Bool(true))),
        )
    }
}

pub struct FnDecl {
    pub regions: Vec<UniversalRegion>,
    pub in_heap: Heap,
    pub inputs: Vec<(Local, Location)>,
    pub out_heap: Heap,
    pub outputs: Vec<(Local, Location)>,
    pub output: Location,
}

#[derive(Clone)]
pub enum Refine {
    Infer,
    Pred(Pred),
}

pub struct Heap(Vec<(Location, Ty)>);

wrap_iterable! {
    Heap: Vec<(Location, Ty)>
}

#[derive(Eq, PartialEq, Clone, Debug)]
pub enum Region {
    Concrete(Vec<Place>),
    Infer,
    Universal(UniversalRegion),
}

newtype_index! {
    struct UniversalRegion
}

impl From<Vec<Place>> for Region {
    fn from(v: Vec<Place>) -> Self {
        Region::Concrete(v)
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Proj {
    Field(usize),
    Deref,
}

#[derive(Eq, PartialEq, Clone, Debug, Hash)]
pub struct Place {
    pub base: Local,
    pub projs: Vec<Proj>,
}

impl Place {
    pub fn new(base: Local, projs: Vec<Proj>) -> Self {
        Self { base, projs }
    }
}

impl Place {
    pub fn overlaps(&self, place: &Place) -> bool {
        if self.base != place.base {
            return false;
        }
        for (proj1, proj2) in self.projs.iter().zip(&place.projs) {
            if proj1 != proj2 {
                return false;
            }
        }
        true
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{}", self.base);
        let mut need_parens = false;
        for proj in &self.projs {
            match proj {
                Proj::Field(n) => {
                    if need_parens {
                        s = format!("({}).{}", s, n);
                        need_parens = false;
                    } else {
                        s = format!("{}.{}", s, n);
                    }
                }
                Proj::Deref => {
                    s = format!("*{}", s);
                    need_parens = true;
                }
            }
        }
        write!(f, "{}", s)
    }
}

impl From<Local> for Place {
    fn from(base: Local) -> Self {
        Place {
            base,
            projs: vec![],
        }
    }
}
