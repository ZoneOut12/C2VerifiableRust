fn fun(x: i32, y: i32, r: &mut i32) -> i32 {
    *r = x;
    let mut d: i32 = 0;
    while *r >= y {
        *r = *r - y;
        d = d + 1;
    }
    d
}