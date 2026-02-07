fn unknown() -> i32 {
    unimplemented!();
}

fn foo(n: i32) {
    let mut c: i32 = 0;

    while unknown() != 0 {
        if unknown() != 0 {
            if c != n {
                if c >= 2147483647 {
                    break;
                }
                c += 1;
            }
        } else {
            if c == n {
                c = 1;
            }
        }
    }
    if c == n {
        // verus_assert(1);
    }
}