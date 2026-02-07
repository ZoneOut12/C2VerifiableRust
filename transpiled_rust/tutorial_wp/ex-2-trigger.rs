fn f(p: &i32, l: u32) {
    unimplemented!();
}

fn g(p: &i32, l: u32) {
    f(p, l);
    f(p, l);
}