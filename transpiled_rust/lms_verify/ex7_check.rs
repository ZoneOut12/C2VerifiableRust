fn member(x0: &[i32], x1: i32, x2: i32) -> i32 {
    let mut x4: i32 = -1;
    let mut x6: i32 = 0;
    while x6 < x1 {
        let x7: i32 = x4;
        let x8: i32 = if x7 == -1 { 1 } else { 0 };
        let x11: i32;
        if x8 != 0 {
            let x9: i32 = x0[x6 as usize];
            let x10: i32 = if x9 == x2 { 1 } else { 0 };
            x11 = x10;
        } else {
            x11 = 0;
        }
        if x11 != 0 {
            x4 = x6;
        }
        x6 += 1;
    }
    let x50: i32 = x4;
    x50
}