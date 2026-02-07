fn index_(x0: i32, x1: i32, x2: i32, x3: i32) -> i32 {
    let x5: i32 = x2 * x1;
    let x6: i32 = x5 + x3;
    x6
}

fn add(x63: &[i32], x64: i32, x65: i32, x66: &[i32], x67: i32, x68: i32, x69: &mut [i32], x70: i32, x71: i32) {
    // verus_assert(1);
    // verus_assert(2);
    let x73: i32 = x70 * x71;
    let mut x81: i32 = 0;
    while x81 < x73 {
        let x94: i32 = x63[x81 as usize];
        let x95: i32 = x66[x81 as usize];
        let x96: i32 = if x94 != 0 || x95 != 0 { 1 } else { 0 };
        x69[x81 as usize] = x96;
        // verus_assert(3);
        // verus_assert(4);
        x81 += 1;
    }
}

fn scalar_mult(x171: i32, x172: &[i32], x173: i32, x174: i32, x175: &mut [i32], x176: i32, x177: i32) {
    // verus_assert(5);
    let x179: i32 = x176 * x177;
    let mut x184: i32 = 0;
    while x184 < x179 {
        let x197: i32;
        if x171 != 0 {
            let x196: i32 = x172[x184 as usize];
            x197 = x196;
        } else {
            x197 = 0;
        }
        x175[x184 as usize] = x197;
        // verus_assert(6);
        x184 += 1;
    }
}