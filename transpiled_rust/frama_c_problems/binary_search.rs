fn binsearch(base: &[i32], n: i32, key: i32) -> i32 {
    let mut l: i32 = 0;
    let mut h: i32 = n - 1;

    while l <= h {
        let m: i32 = l + (h - l) / 2;
        let val: i32 = base[m as usize];

        if val < key {
            l = m + 1;
            // verus_assert(1);
            // verus_assert(2);
        } else if val > key {
            h = m - 1;
        } else {
            // verus_assert(3);
            return m;
        }
    }

    -1
}