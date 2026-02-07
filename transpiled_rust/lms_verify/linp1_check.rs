fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> i32 {
    let x5: i32 = x2 * x1;
    let x6: i32 = x5 + x3;
    x6
}

fn mult(x63: &[i32], x64: i32, x65: i32, x66: &[i32], x67: i32, x68: i32, x69: &mut [i32], x70: i32, x71: i32) {
    let mut x76: i32 = 0;
    while x76 < x64 {
        let mut x78: i32 = 0;
        while x78 < x68 {
            let x79: i32 = index_(x70, x71, x76, x78);
            x69[x79 as usize] = 0;
            let mut x82: i32 = 0;
            while x82 < x65 {
                let x83: i32 = x69[x79 as usize];
                let x84: i32 = index_(x64, x65, x76, x82);
                let x85: i32 = x63[x84 as usize];
                let x88: i32;
                if x85 != 0 {
                    let x86: i32 = index_(x67, x68, x82, x78);
                    let x87: i32 = x66[x86 as usize];
                    x88 = x87;
                } else {
                    x88 = 0;
                }
                let x89: i32 = if (x83 != 0) || (x88 != 0) { 1 } else { 0 };
                x69[x79 as usize] = x89;
                x82 += 1;
            }
            x78 += 1;
        }
        x76 += 1;
    }
}