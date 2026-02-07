fn pick_index(n: i32) -> i32 {
    0
}

fn pick_element(p: &[i32], n: i32) -> i32 {
    let i: i32 = pick_index(n);
    // verus_assert(1);
    // verus_assert(2);
    p[i as usize]
}

fn pick_first(p: &[i32]) -> i32 {
    p[0]
}