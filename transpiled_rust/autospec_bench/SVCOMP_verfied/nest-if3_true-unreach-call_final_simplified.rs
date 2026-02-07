fn unknown1() -> i32 {
    unimplemented!();
}

fn foo(n: i32, mut l: i32) {
    let mut k: i32;
    let mut i: i32;

    k = 1;
    while k < n {
        i = l;
        while i < n {
            // verus_assert(1);
            i += 1;
        }
        if unknown1() != 0 && l < 2147483647 {
            l = l + 1;
        }
        k += 1;
    }
}