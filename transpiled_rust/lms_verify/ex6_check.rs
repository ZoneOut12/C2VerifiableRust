fn inswap(x0: &mut [i32], x1: i32, x2: i32) {
    let x4: i32 = x0[x1 as usize];
    let x5: i32 = x0[x2 as usize];
    x0[x1 as usize] = x5;
    x0[x2 as usize] = x4;
}

fn insort(x22: &mut [i32], x23: i32) {
    let mut x26: i32 = x23;
    while true {
        let x27: i32 = x26;
        let x28: bool = x27 > 1;
        if !x28 {
            break;
        }
        let mut x30: i32 = 0;
        let x31: i32 = x26;
        let mut x33: i32 = 0;
        while x33 < x31 {
            let x34: i32 = x22[x33 as usize];
            let x35: i32 = x30;
            let x36: i32 = x22[x35 as usize];
            let x37: bool = x34 >= x36;
            if x37 {
                x30 = x33;
            } else {
            }
            x33 += 1;
        }
        let x82: i32 = x30;
        let x81: i32 = x31 - 1;
        inswap(x22, x81, x82);
        // verus_assert(1);
        // verus_assert(2);
        // verus_assert(3);
        x26 = x81;
    }
}