fn reverse(a: &mut [i32], n: i32) {
    let mut i: i32 = 0;
    let mut j: i32 = n - 1;
    
    while i < n / 2 {
        let temp: i32 = a[i as usize];
        a[i as usize] = a[j as usize];
        a[j as usize] = temp;
        i += 1;
        j -= 1;
    }
}