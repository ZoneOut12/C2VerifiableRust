fn abs(x: i32) -> i32 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn square(x: i32) -> u32 {
    let v: u32 = abs(x) as u32;
    v * v
}