fn g(x: &mut i32) {
    unimplemented!();
}

fn example(x: &mut i32) {
    g(x);
    // verus_assert(1);
    // verus_assert(2);
}