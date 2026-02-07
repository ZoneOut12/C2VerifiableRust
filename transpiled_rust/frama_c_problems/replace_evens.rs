fn func(a: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    while i < n {
        if i % 2 == 0 {
            a[i as usize] = 0;
        }
        i += 1;
    }
}