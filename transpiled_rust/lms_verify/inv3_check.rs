fn count_pos(x15: &[i32], x16: i32) -> i32 {
    let mut x18: i32 = 0;
    let mut x20: i32 = 0;
    while x20 < x16 {
        let x22: i32 = x18;
        let x21: i32 = x15[x20 as usize];
        let x26: bool = x21 > 0;
        let x27: i32;
        if x26 {
            x27 = 1;
        } else {
            x27 = 0;
        }
        let x28: i32 = x22 + x27;
        x18 = x28;
        x20 += 1;
    }
    let x32: i32 = x18;
    x32
}