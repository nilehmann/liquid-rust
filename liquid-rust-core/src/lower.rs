use std::{collections::HashMap, iter::FromIterator};

use ast::ContDef;

use crate::{
    ast::{self, visitor::Visitor, FnDef},
    names::ContId,
    ty::{self, KVid, RegionVid, TyCtxt, Var},
};

pub struct TypeLowerer<'a> {
    tcx: &'a TyCtxt,
    vars_in_scope: Vec<Var>,
    conts: HashMap<ContId, ty::ContTy>,
}

impl<I> Visitor<I> for TypeLowerer<'_> {
    fn visit_cont_def(&mut self, def: &ContDef<I>) {
        let cont_ty = self.lower_cont_ty(&def.ty);

        let len = self.vars_in_scope.len();
        self.vars_in_scope
            .extend(cont_ty.heap.iter().map(|(l, _)| Var::from(*l)));
        self.visit_fn_body(&def.body);
        self.vars_in_scope.truncate(len);

        self.conts.insert(def.name, cont_ty);
    }
}

impl<'a> TypeLowerer<'a> {
    fn new(tcx: &'a TyCtxt) -> Self {
        Self {
            tcx,
            vars_in_scope: Vec::new(),
            conts: HashMap::new(),
        }
    }

    pub fn lower_fn_def<I>(
        tcx: &TyCtxt,
        func: &FnDef<I>,
    ) -> (HashMap<ContId, ty::ContTy>, ty::FnDecl) {
        let mut lowerer = TypeLowerer::new(tcx);
        let fn_ty = lowerer.lower_fn_ty(&func.ty);
        let ret_cont_ty = ty::ContTy::new(
            lowerer.lower_heap(&func.ty.out_heap),
            func.ty
                .outputs
                .iter()
                .zip(&func.params)
                .map(|((_, l), x)| (*x, *l))
                .collect(),
            vec![func.ty.output],
        );
        lowerer.vars_in_scope.extend(fn_ty.in_heap.vars_in_scope());
        lowerer.visit_fn_body(&func.body);
        lowerer.conts.insert(func.ret, ret_cont_ty);
        (lowerer.conts, fn_ty)
    }

    fn lower_ty(&mut self, ty: &ast::Ty) -> ty::Ty {
        match ty {
            ast::Ty::OwnRef(location) => self.tcx.mk_own_ref(*location),
            ast::Ty::Ref(bk, region, location) => {
                self.tcx.mk_ref(*bk, self.lower_region(region), *location)
            }
            ast::Ty::Tuple(tup) => {
                let mut vec = Vec::new();
                let len = self.vars_in_scope.len();
                for (f, ty) in tup {
                    vec.push((*f, self.lower_ty(ty)));
                    self.vars_in_scope.push(Var::Field(*f));
                }
                self.vars_in_scope.truncate(len);
                self.tcx.mk_tuple(ty::Tuple::from_iter(vec))
            }
            ast::Ty::Uninit(n) => self.tcx.mk_uninit(*n),
            ast::Ty::Refine(bty, refine) => self.tcx.mk_refine(*bty, self.lower_refine(refine)),
        }
    }

    fn lower_cont_ty(&mut self, cont_ty: &ast::ContTy) -> ty::ContTy {
        ty::ContTy::new(
            self.lower_heap(&cont_ty.heap),
            cont_ty.locals.iter().copied().collect(),
            cont_ty.inputs.clone(),
        )
    }

    fn lower_fn_ty(&mut self, fn_ty: &ast::FnDecl) -> ty::FnDecl {
        ty::FnDecl {
            regions: fn_ty.regions.clone(),
            in_heap: self.lower_heap(&fn_ty.in_heap),
            inputs: fn_ty.inputs.iter().copied().collect(),
            out_heap: self.lower_heap(&fn_ty.out_heap),
            outputs: fn_ty.outputs.iter().copied().collect(),
            output: fn_ty.output,
        }
    }

    fn lower_heap(&mut self, heap: &ast::Heap) -> ty::Heap {
        let len = self.vars_in_scope.len();
        let heap = heap
            .into_iter()
            .map(|(l, ty)| {
                let r = (*l, self.lower_ty(ty));
                self.vars_in_scope.push(Var::from(*l));
                r
            })
            .collect();
        self.vars_in_scope.truncate(len);
        heap
    }

    fn lower_region(&mut self, region: &ast::Region) -> ty::Region {
        match region {
            ast::Region::Concrete(places) => ty::Region::Concrete(places.clone()),
            ast::Region::Infer => ty::Region::Infer(self.tcx.fresh::<RegionVid>()),
            ast::Region::Universal(param) => ty::Region::Universal(*param),
        }
    }

    fn lower_refine(&self, refine: &ast::Refine) -> ty::Refine {
        match refine {
            ast::Refine::Pred(pred) => ty::Refine::Pred(self.lower_pred(pred)),
            ast::Refine::Infer => {
                let mut vars_in_scope = vec![Var::Nu];
                vars_in_scope.extend(&self.vars_in_scope);
                ty::Refine::Infer(ty::Kvar(self.tcx.fresh::<KVid>(), vars_in_scope))
            }
        }
    }

    fn lower_pred(&self, pred: &ast::Pred) -> ty::Pred {
        match pred {
            ast::Pred::Constant(c) => self.tcx.mk_constant(*c),
            ast::Pred::Place(place) => self.tcx.mk_pred_place(place.clone()),
            ast::Pred::BinaryOp(bin_op, op1, op2) => {
                self.tcx
                    .mk_bin_op(*bin_op, self.lower_pred(op1), self.lower_pred(op2))
            }
            ast::Pred::UnaryOp(un_op, op) => self.tcx.mk_un_op(*un_op, self.lower_pred(op)),
        }
    }
}
