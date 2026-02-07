fn unknown() -> i32 {
    unimplemented!();
}

fn foo(mut x: i32, mut y: i32) {
    let mut lock: i32 = 1;
    while x != y {
        if unknown() != 0 {
            lock = 1;
            x = y;
        } else {
            lock = 0;
            x = y;
            y = y + 1;
        }
    }
    // verus_assert(1);
}