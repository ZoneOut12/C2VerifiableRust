fn func(c: i32) -> i32 {
    let mut x: i32 = c;
    let mut y: i32 = 0;
    while x > 0 {
        x = x - 1;
        y = y + 1;
    }
    y
}