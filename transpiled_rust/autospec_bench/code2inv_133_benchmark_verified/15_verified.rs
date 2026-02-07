fn unknown() -> i32 {
    unimplemented!();
}

fn foo(n: i32) {
    let mut x: i32 = 0;
    let mut m: i32 = 0;

    while x < n {
        if unknown() != 0 {
            m = x;
        }
        x = x + 1;
    }

    if n > 0 {
        // verus_assert(1);
        // verus_assert(2);
    }
}