use rustc_data_structures::fx::FxIndexSet;
use rustc_data_structures::graph::scc::Sccs;
use rustc_data_structures::graph::{DirectedGraph, Successors};
use rustc_hir as hir;
use rustc_index::{IndexVec, newtype_index};
use rustc_middle::mir::interpret::{AllocId, Allocation, ConstAllocation, GlobalAlloc};
use rustc_middle::ty::TyCtxt;
use rustc_span::ErrorGuaranteed;
use rustc_span::def_id::LocalDefId;

// Graph indices
newtype_index! {
    struct StaticNodeIdx {}
}
newtype_index! {
    #[derive(Ord, PartialOrd)]
    struct StaticSccIdx {}
}

// Adjacency-list graph
struct StaticRefGraph {
    succ: IndexVec<StaticNodeIdx, Vec<StaticNodeIdx>>,
}

impl DirectedGraph for StaticRefGraph {
    type Node = StaticNodeIdx;

    fn num_nodes(&self) -> usize {
        self.succ.len()
    }
}

impl Successors for StaticRefGraph {
    fn successors(&self, n: StaticNodeIdx) -> impl Iterator<Item = StaticNodeIdx> {
        self.succ[n].iter().copied()
    }
}

pub(crate) fn check_static_initializer_acyclic(
    tcx: TyCtxt<'_>,
    _: (),
) -> Result<(), ErrorGuaranteed> {
    // Collect local statics
    let statics: FxIndexSet<LocalDefId> = tcx
        .hir_free_items()
        .filter_map(|item_id| {
            let item = tcx.hir_item(item_id);
            match item.kind {
                hir::ItemKind::Static(..) => Some(item.owner_id.def_id),
                _ => None,
            }
        })
        .collect();

    // Fast path
    if statics.is_empty() {
        return Ok(());
    }

    // For all statics collect all reachable statics to create a graph
    let graph = StaticRefGraph {
        succ: statics
            .iter()
            .map(|&id| {
                if let Ok(root_alloc) = tcx.eval_static_initializer(id) {
                    collect_referenced_local_statics(tcx, root_alloc, &statics)
                } else {
                    Vec::new()
                }
            })
            .collect(),
    };

    // Calculate all SCCs from the graph
    let sccs: Sccs<StaticNodeIdx, StaticSccIdx> = Sccs::new(&graph);
    // Group statics by SCCs
    let mut members: IndexVec<StaticSccIdx, Vec<StaticNodeIdx>> =
        IndexVec::from_elem_n(Vec::new(), sccs.num_sccs());
    for i in graph.succ.indices() {
        members[sccs.scc(i)].push(i);
    }
    let mut first_guar: Option<ErrorGuaranteed> = None;

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

        let head_def = statics[usize::from(nodes[0])];
        let head_span = tcx.def_span(head_def);

        let mut diag = tcx.dcx().struct_span_err(
            head_span,
            format!(
                "static initializer forms a cycle involving `{}`",
                tcx.def_path_str(head_def.to_def_id()),
            ),
        );
        diag.span_labels(
            nodes.iter().map(|&n| tcx.def_span(statics[usize::from(n)])),
            "part of this cycle",
        )
        .note(format!(
            "cyclic static initializer references are not supported for target `{}`",
            tcx.sess.target.llvm_target
        ));
        first_guar.get_or_insert(diag.emit());
    }

    match first_guar {
        Some(g) => Err(g),
        None => Ok(()),
    }
}

// Traverse allocations reachable from the static initializer allocation and collect local-static targets.
fn collect_referenced_local_statics<'tcx>(
    tcx: TyCtxt<'tcx>,
    root_alloc: ConstAllocation<'tcx>,
    statics: &FxIndexSet<LocalDefId>,
) -> Vec<StaticNodeIdx> {
    let mut referenced_nodes: Vec<StaticNodeIdx> = Vec::default();
    let mut alloc_ids: FxIndexSet<AllocId> = FxIndexSet::default();

    let add_ids_from_alloc = |alloc: &Allocation, ids: &mut FxIndexSet<AllocId>| {
        ids.extend(alloc.provenance().ptrs().iter().map(|(_, prov)| prov.alloc_id()));
    };

    // Scan the root allocation for pointers first.
    add_ids_from_alloc(root_alloc.inner(), &mut alloc_ids);

    for i in 0.. {
        let Some(&alloc_id) = alloc_ids.get_index(i) else {
            break;
        };
        match tcx.try_get_global_alloc(alloc_id) {
            Some(GlobalAlloc::Static(def_id)) => {
                if let Some(local_def) = def_id.as_local()
                    && let Some(node) = statics.get_index_of(&local_def)
                {
                    referenced_nodes.push(node.into());
                }
            }
            Some(GlobalAlloc::Memory(const_alloc)) => {
                add_ids_from_alloc(const_alloc.inner(), &mut alloc_ids);
            }
            _ => {} // Functions, vtables, etc: ignore
        }
    }
    referenced_nodes
}
