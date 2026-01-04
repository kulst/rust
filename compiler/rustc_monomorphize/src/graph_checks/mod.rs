use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::TyCtxt;

use crate::collector::UsageMap;
use crate::graph_checks::statics_check::check_static_initializers_are_acyclic;

mod statics_check;

pub(super) fn check_mono_item_graph<'tcx, 'a, 'b>(
    tcx: TyCtxt<'tcx>,
    mono_items: &'a [MonoItem<'tcx>],
    usage_map: &'b UsageMap<'tcx>,
) {
    do_target_specific_checks(tcx, mono_items, usage_map);
}

fn do_target_specific_checks<'tcx, 'a, 'b>(
    tcx: TyCtxt<'tcx>,
    mono_items: &'a [MonoItem<'tcx>],
    usage_map: &'b UsageMap<'tcx>,
) {
    if tcx.sess.target.options.static_initializer_must_be_acyclic {
        check_static_initializers_are_acyclic(tcx, mono_items, usage_map);
    }
}
