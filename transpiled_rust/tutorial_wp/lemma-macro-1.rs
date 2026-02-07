fn bsearch(arr: &mut [i32], len: usize, value: i32) -> usize {
    unimplemented!();
}

fn bsearch_callee(arr: &mut [i32], len: usize, value: i32) -> usize {
    // verus_assert(1);
    let mut i: usize = 0;
    while i < len {
        // verus_assert(2);
        i += 1;
    }
    // verus_assert(3);
    bsearch(arr, len, value)
}