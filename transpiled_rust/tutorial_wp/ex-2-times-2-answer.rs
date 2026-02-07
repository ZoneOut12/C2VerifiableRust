fn times_2(mut x: i32) -> i32 {
    let mut r: i32 = 0;
    let mut i: i32 = 0;

    while x > 0 {
        r += 2;
        x -= 1;
        i += 1;
    }
    return r;
}