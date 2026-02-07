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
        if x13 == 0 {
            break;
        }
        let x39 = x5;
        let x40 = unsafe { x39.offset(1) };
        x5 = x40;
        
    }
    let x86 = x5;
    let x87 = unsafe { *x86 as i8 };
    let x88 = x87 == 0;
    let x91;
    if x88 {
        let x89 = x2;
        x91 = x89;
    } else {
        x91 = 0;
    }
    let x95;
    if x91 != 0 {
        let x92 = x3;
        let x93 = x92 == 3;
        x95 = x93 as i32;
    } else {
        x95 = 0;
    }
    // verus_assert(1);
    x95
}