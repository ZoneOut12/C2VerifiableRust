fn bsearch(arr: &[i32], len: usize, value: i32) -> usize {
    unimplemented!();
}

fn bsearch_callee(arr: &[i32], len: usize, value: i32) -> usize {
    let mut i: usize = 0;
    while i < len {
        // verus_assert(1);
        i += 1;
    }
    bsearch(arr, len, value)
}