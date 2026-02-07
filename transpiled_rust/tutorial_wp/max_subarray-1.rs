fn max_subarray(a: &[i32], len: usize) -> i32 {
    let mut max: i32 = 0;
    let mut cur: i32 = 0;
    let mut cur_low: usize = 0;
    let mut low: usize = 0;
    let mut high: usize = 0;

    let mut i: usize = 0;
    while i < len {
        // verus_assert(1);
        cur += a[i];
        if cur < 0 {
            cur = 0;
            cur_low = i + 1;
        }
        if cur > max {
            max = cur;
            low = cur_low;
            high = i + 1;
        }
        i += 1;
    }
    max
}