fn func(n: i32) -> i32 {
    let mut sum: i32 = 0;
    let mut i: i32 = 0;
    
    while i <= n / 2 {
        sum = sum + 2 * i;
        i += 1;
    }
    // verus_assert(1);
    sum
}