fn unknown() -> i32 {
    unimplemented!();
}

fn foo(mut x: i32, mut y: i32) {
    while unknown() != 0 {
        if x > i32::MAX - 10 || y > i32::MAX - 10 {
            break;
        }
        x = x + 10;
        y = y + 10;
    }
    if x == 20 {
        // verus_assert(1);
    }
}