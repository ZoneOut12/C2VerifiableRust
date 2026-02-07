fn max(x0: i32, x1: i32) -> i32 {
    let x3: i32 = (x0 > x1) as i32;
    let x4: i32;
    if x3 != 0 {
        x4 = x0;
    } else {
        x4 = x1;
    }
    x4
}