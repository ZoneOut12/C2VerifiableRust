const INT_MAX: i32 = i32::MAX;

fn dfa(x0: &str) -> i32 {
    let mut x2 = 1;
    let mut x3 = 0;
    
    let mut x5 = x0.as_ptr();
    
    loop {
        let x7 = x5;
        let x8 = unsafe { *x7 as i8 };
        let x9 = x8 == 0;
        let x13;
        if x9 {
            x13 = 0;
        } else {
            let x11 = x2;
            x13 = x11;
        }
        if x13 == 0 { break; }
        let x41 = x5;
        let x42 = unsafe { x41.offset(1) };
        x5 = x42;
    }
    let x88 = x5;
    let x89 = unsafe { *x88 as i8 };
    let x90 = x89 == 0;
    let x93;
    if x90 {
        let x91 = x2;
        x93 = x91;
    } else {
        x93 = 0;
    }
    let x97;
    if x93 != 0 {
        let x94 = x3;
        let x95 = x94 == 4;
        x97 = x95 as i32;
    } else {
        x97 = 0;
    }
    // verus_assert(1);
    x97
}