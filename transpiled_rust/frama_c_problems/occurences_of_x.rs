fn func(a: &[i32], n: i32, x: i32, sum: &mut i32) -> i32 {
    let mut p: i32 = 0;
    let mut count: i32 = 0;
    *sum = 0;
    
    while p < n {
        if a[p as usize] == x {
            count = count + 1;
            *sum = *sum + x;
        }
        p = p + 1;
    }
    // Label_a:
    *sum += 0;
    // verus_assert(1);
    count
}