fn f(p: &mut [i32], l: u32) {
    unimplemented!();
}

fn g(p: &mut [i32], l: u32) {
    f(p, l);
    // verus_assert(1);
    f(p, l);
}