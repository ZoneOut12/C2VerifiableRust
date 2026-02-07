fn sum_42(n: i32) -> i32 {
    let mut x: i32 = 0;
    let r: i32 = 42;
    
    let mut i: i32 = 0;
    while i < n {
        x += r;
        i += 1;
    }
    x
}