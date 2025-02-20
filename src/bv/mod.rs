mod small;

pub(crate) fn register_bitvec_sorts(egraph: &mut egglog::EGraph) {
    small::register_small_bitvec_sort(egraph);
}
