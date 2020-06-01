use crate::context::LiquidRustCtxt;
use crate::syntax::ast::{BinOpKind, UnOpKind};
use super::{Operand, Pred};
use rustc_data_structures::graph::vec_graph::VecGraph;
use rustc_middle::mir;
use std::collections::HashMap;

pub struct DominatorTree<'lr, 'tcx> {
    /// The dominator tree, generated from the control-flow graph of the
    /// bbs in the function
    pub dom_tree: VecGraph<mir::BasicBlock>,

    /// The new predicates which we know for sure to be true before entering
    /// a basic block
    pub known_preds: HashMap<mir::BasicBlock, &'lr Pred<'lr, 'tcx>>,
}

impl<'lr, 'tcx> DominatorTree<'lr, 'tcx> {
    /// Transforms the control flow graph into a dominator tree, which is used
    /// so that we can later do a depth-first traversal in dominator-tree-order
    /// when type-checking the body of this function.
    ///
    /// The dominator tree also contains edge information - predicates which
    /// we know to be true after we've travelled along an edge.
    pub fn build(
        cx: &LiquidRustCtxt<'lr, 'tcx>,
        body: &mir::Body<'tcx>,
    ) -> DominatorTree<'lr, 'tcx> {
        let mut edges = Vec::new();
        let mut known_preds = HashMap::new();
        let dominators = body.dominators();

        for (bb, bbd) in body.basic_blocks().iter_enumerated() {
            let dr = dominators.immediate_dominator(bb);
            if dr != bb {
                edges.push((dr, bb));
            }

            if let Some(terminator) = &bbd.terminator {
                match &terminator.kind {
                    mir::TerminatorKind::SwitchInt {
                        discr,
                        values,
                        switch_ty,
                        targets,
                    } => {
                        let discr = cx.mk_operand(Operand::from_mir(discr));
                        let mut disj = cx.pred_false;
                        for (value, target) in values.iter().zip(targets.iter()) {
                            let value = cx.mk_operand(Operand::from_bits(
                                cx.tcx(),
                                *value,
                                switch_ty,
                            ));
                            let cond = cx.mk_binary(discr, BinOpKind::Eq, value);
                            disj = cx.mk_binary(disj, BinOpKind::Or, cond);
                            known_preds.insert(*target, cond);
                        }

                        // There will always be one more target than there are
                        // values: this represents the "otherwise" case.
                        let otherwise_bb = targets.last().unwrap();
                        let neg = cx.mk_unary(UnOpKind::Not, disj);
                        known_preds.insert(*otherwise_bb, neg);
                    }
                    mir::TerminatorKind::Assert {
                        cond,
                        expected,
                        target,
                        ..
                    } => {
                        let mut cond = cx.mk_operand(Operand::from_mir(cond));
                        if !expected {
                            cond = cx.mk_unary(UnOpKind::Not, cond);
                        }
                        known_preds.insert(*target, cond);
                    }
                    _ => {}
                }
            }
        }

        return DominatorTree {
            known_preds,
            dom_tree: VecGraph::new(body.basic_blocks().len(), edges),
        };
    }

    pub fn traverse<'dt>(
        &'dt self, start_node: mir::BasicBlock
    ) -> DepthFirstTraversal<'dt, 'lr, 'tcx> {
        DepthFirstTraversal::with_start_node(&self, start_node)
    }
}

pub struct DepthFirstTraversal<'dt, 'lr, 'tcx> {
    dom_tree: &'dt DominatorTree<'lr, 'tcx>,
    queue: Vec<(usize, mir::BasicBlock)>,
}

impl<'dt, 'lr, 'tcx> DepthFirstTraversal<'dt, 'lr, 'tcx> {
    pub fn with_start_node(
        dom_tree: &'dt DominatorTree<'lr, 'tcx>, start_node: mir::BasicBlock
    ) -> Self {
        let queue = vec![(1, start_node)];

        DepthFirstTraversal { dom_tree, queue }
    }
}

impl<'dt, 'lr, 'tcx> Iterator for DepthFirstTraversal<'dt, 'lr, 'tcx> {
    type Item = (usize, Option<&'lr Pred<'lr, 'tcx>>, mir::BasicBlock);

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.queue.pop();
        if let Some((depth, bb)) = next {
            for domd in self.dom_tree.dom_tree.successors(bb) {
                self.queue.push((depth + 1, *domd));
            }
            let pred = self.dom_tree.known_preds.get(&bb);
            Some((depth, pred.map(|x| *x), bb))
        } else {
            None
        }
    }
}
