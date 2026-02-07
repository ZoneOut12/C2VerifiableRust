fn occ_not_zero_some_is_v(v: i32, r#in: &[i32], len: usize) -> usize {
    let mut i: usize = 0;
    while i < len {
        if r#in[i] == v {
            return i;
        }
        i += 1;
    }
    // verus_assert(1);
    usize::MAX
}

fn foo(v: i32, r#in: &[i32], len: usize) {
    let witness: usize = occ_not_zero_some_is_v(v, r#in, len);
    // verus_assert(2);
}