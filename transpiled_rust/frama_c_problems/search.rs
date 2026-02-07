fn arraysearch(a: &[i32], x: i32, n: i32) -> i32 {
    let mut p: i32 = 0;
    while p < n {
        if a[p as usize] == x {
            return 1;
        }
        p += 1;
    }
    0
}