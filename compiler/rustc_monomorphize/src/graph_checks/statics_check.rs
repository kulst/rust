use rustc_data_structures::fx::FxIndexSet;
use rustc_data_structures::graph::scc::Sccs;
use rustc_data_structures::graph::{DirectedGraph, Successors};
use rustc_data_structures::unord::UnordMap;
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec, newtype_index};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::TyCtxt;

use crate::collector::UsageMap;

// // Graph indices
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct StaticNodeIdx(usize);

impl Idx for StaticNodeIdx {
    fn new(idx: usize) -> Self {
        Self(idx)
    }

    fn index(self) -> usize {
        self.0
    }
}

impl From<usize> for StaticNodeIdx {
    fn from(value: usize) -> Self {
        StaticNodeIdx(value)
    }
}

newtype_index! {
    #[derive(Ord, PartialOrd)]
    struct StaticSccIdx {}
}

// Adjacency-list graph
struct StaticRefGraph<'a, 'b, 'tcx> {
    statics: &'a FxIndexSet<DefId>,
    used_map: &'b UnordMap<MonoItem<'tcx>, Vec<MonoItem<'tcx>>>,
}

impl<'a, 'b, 'tcx> DirectedGraph for StaticRefGraph<'a, 'b, 'tcx> {
    type Node = StaticNodeIdx;

    fn num_nodes(&self) -> usize {
        self.statics.len()
    }
}

impl<'a, 'b, 'tcx> Successors for StaticRefGraph<'a, 'b, 'tcx> {
    fn successors(&self, node_idx: StaticNodeIdx) -> impl Iterator<Item = StaticNodeIdx> {
        let def_id = self.statics[node_idx.index()];
        self.used_map[&MonoItem::Static(def_id)].iter().filter_map(|&mono_item| match mono_item {
            MonoItem::Static(def_id) => self.statics.get_index_of(&def_id).map(|idx| idx.into()),
            _ => None,
        })
    }
}

pub(super) fn check_static_initializers_are_acyclic<'tcx, 'a, 'b>(
    tcx: TyCtxt<'tcx>,
    mono_items: &'a [MonoItem<'tcx>],
    usage_map: &'b UsageMap<'tcx>,
) {
    // Collect statics
    let statics: FxIndexSet<DefId> = mono_items
        .iter()
        .filter_map(|&mono_item| match mono_item {
            MonoItem::Static(def_id) => Some(def_id),
            _ => None,
        })
        .collect();

    // Fast path
    if statics.is_empty() {
        return;
    }
    // For all statics collect all reachable statics to create a graph
    let graph = StaticRefGraph { statics: &statics, used_map: &usage_map.used_map };

    // // Calculate all SCCs from the graph
    let sccs: Sccs<StaticNodeIdx, StaticSccIdx> = Sccs::new(&graph);
    // // Group statics by SCCs
    let mut members: IndexVec<StaticSccIdx, Vec<StaticNodeIdx>> =
        IndexVec::from_elem_n(Vec::new(), sccs.num_sccs());
    for i in graph.iter_nodes() {
        members[sccs.scc(i)].push(i);
    }
    for scc in sccs.all_sccs() {
        let nodes = &members[scc];
        let acyclic = match nodes.len() {
            0 => true,
            1 => graph.successors(nodes[0]).all(|x| x != nodes[0]),
            2.. => false,
        };

        if acyclic {
            continue;
        }

        let head_def = statics[nodes[0].index()];
        let head_span = tcx.def_span(head_def);

        let mut diag = tcx.dcx().struct_span_err(
            head_span,
            format!("static initializer forms a cycle involving `{}`", tcx.def_path_str(head_def)),
        );
        diag.span_labels(
            nodes.iter().map(|&n| tcx.def_span(statics[n.index()])),
            "part of this cycle",
        )
        .note(format!(
            "cyclic static initializer references are not supported for target `{}`",
            tcx.sess.target.llvm_target
        ));
        let _ = diag.emit();
    }
}
