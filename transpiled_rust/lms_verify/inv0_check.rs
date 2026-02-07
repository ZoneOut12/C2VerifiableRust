fn eq_vec_Int(x15: &[i32], x16: i32, x17: &[i32], x18: i32) -> i32 {
    let x20: i32 = if x16 == x18 { 1 } else { 0 };
    let x31: i32;
    if x20 != 0 {
        let mut x30: i32 = 1;
        let mut x23: i32 = 0;
        while x23 < x16 {
            let x27: i32 = x15[x23 as usize];
            let x28: i32 = x17[x23 as usize];
            let x29: i32 = if x27 == x28 { 1 } else { 0 };
            if x29 == 0 {
                x30 = 0;
                break;
            }
            x23 += 1;
        }
        x31 = x30;
    } else {
        x31 = 0;
    }
    x31
}