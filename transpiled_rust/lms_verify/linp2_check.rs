fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> i32 {
    let x5: i32 = x2 * x1;
    let x6: i32 = x5 + x3;
    x6
}

fn add(x63: &[i32], x64: i32, x65: i32, x66: &[i32], x67: i32, x68: i32, x69: &mut [i32], x70: i32, x71: i32) {
    let mut x76: i32 = 0;
    while x76 < x70 {
        let mut x78: i32 = 0;
        while x78 < x71 {
            let x79: i32 = index_(x64, x65, x76, x78);
            let x80: i32 = x63[x79 as usize];
            let x81: i32 = index_(x67, x68, x76, x78);
            let x82: i32 = x66[x81 as usize];
            let x83: i32 = if (x80 != 0) || (x82 != 0) { 1 } else { 0 };
            let x84: i32 = index_(x70, x71, x76, x78);
            x69[x84 as usize] = x83;
            x78 += 1;
        }
        x76 += 1;
    }
}

fn scalar_mult(x110: i32, x111: &[i32], x112: i32, x113: i32, x114: &mut [i32], x115: i32, x116: i32) {
    let mut x121: i32 = 0;
    while x121 < x115 {
        let mut x123: i32 = 0;
        while x123 < x116 {
            let x126: i32;
            if x110 != 0 {
                let x124: i32 = index_(x112, x113, x121, x123);
                let x125: i32 = x111[x124 as usize];
                x126 = x125;
            } else {
                x126 = 0;
            }
            let x127: i32 = index_(x115, x116, x121, x123);
            x114[x127 as usize] = x126;
            x123 += 1;
        }
        x121 += 1;
    }
}