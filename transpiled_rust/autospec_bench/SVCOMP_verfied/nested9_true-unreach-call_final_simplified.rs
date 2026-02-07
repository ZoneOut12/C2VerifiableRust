fn foo(n: i32, m: i32, l: i32) -> i32 {
    if 3 * n <= m + l {
        let mut i: i32 = 0;
        while i < n {
            let mut j: i32 = 2 * i;
            while j < 3 * i {
                let mut k: i32 = i;
                while k < j {
                    // verus_assert(1);
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
    }
    0
}