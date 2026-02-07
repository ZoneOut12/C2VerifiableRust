fn sum_separable(array: &[i32], begin: usize, split: usize, end: usize) {
    let mut i: usize = split;
    while i < end {
        i += 1;
    }
}

fn inc_cell(array: &mut [i32], len: usize, i: usize) {
    sum_separable(array, 0, i, len);
    sum_separable(array, i, i + 1, len);
    array[i] += 1;
    // verus_assert(1);
    sum_separable(array, 0, i, len);
    sum_separable(array, i, i + 1, len);
    // verus_assert(1);
    
    let mut _i: usize = 0;
    while _i < i {
        _i += 1;
    }
    // verus_assert(2);
    
    // verus_assert(3);
    
    let mut _i: usize = i + 1;
    while _i < len {
        _i += 1;
    }
    // verus_assert(4);
}