fn bsearch(arr: &mut [i32], len: usize, value: i32) -> usize {
    unimplemented!();
}

fn element_level_sorted_implies_sorted(arr: &[i32], len: usize) {
    let mut i: usize = 0;
    while i < len {
        // verus_assert(1);
        i += 1;
    }
}

fn bsearch_callee(arr: &mut [i32], len: usize, value: i32) -> u32 {
    element_level_sorted_implies_sorted(arr, len);
    bsearch(arr, len, value) as u32
}