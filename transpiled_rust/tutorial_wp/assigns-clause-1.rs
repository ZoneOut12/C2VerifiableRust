static mut x: i32 = 0;

fn ghost_foo() {
    unimplemented!();
}

fn foo() {
    let mut i: i32 = 0;
    while i < 10 {
        i += 1;
    }
}