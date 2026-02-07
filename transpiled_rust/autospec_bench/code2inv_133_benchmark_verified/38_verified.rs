fn unknown() -> i32 {
    unimplemented!();
}

fn foo(n: i32) {
    let mut c: i32 = 0;
    while unknown() != 0 {
        if c == n {
            c = 1;
        } else {
            c = c + 1;
        }
    }
    if c == n {
        // verus_assert(1);
    }
}