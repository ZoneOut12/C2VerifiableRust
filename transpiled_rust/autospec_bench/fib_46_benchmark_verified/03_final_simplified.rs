fn foo(n: i32, l: i32) {
    let mut i: i32;
    let mut k: i32;

    k = 1;
    while k < n {
        i = l;
        while i < n {
            i += 1;
        }

        i = l;
        while i < n {
            // verus_assert(1);
            i += 1;
        }

        k += 1;
    }
}