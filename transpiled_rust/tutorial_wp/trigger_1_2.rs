fn g(x: &mut i32) {
    unimplemented!();
}

fn example(x: &mut i32, y: &mut i32) {
    g(y);
    // verus_assert(1);
}