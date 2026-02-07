fn arraymax(a: &[i32], n: i32) -> i32 {
    let mut i: i32 = 1;
    let mut max: i32 = a[0];
    
    while i < n {
        if max < a[i as usize] {
            max = a[i as usize];
            // verus_assert(1);
        }
        i = i + 1;
    }
    max
}