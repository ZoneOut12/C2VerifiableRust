const INT_MAX: i32 = i32::MAX;

fn dfa(x0: &str) -> i32 {
    let mut x2 = 1;
    let mut x3 = 0;
    
    let mut x5 = x0.as_ptr();
    
    loop {
        let x7 = x5;
        let x8 = unsafe { *x7 as u8 };
        let x9 = x8 == b'\0' as u8;
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
        let x37 = x5;
        let x38 = unsafe { x37.offset(1) };
        x5 = x38;
        
    }
    let x84 = x5;
    let x85 = unsafe { *x84 as u8 };
    let x86 = x85 == b'\0' as u8;
    let x89;
    if x86 {
        let x87 = x2;
        x89 = x87;
    } else {
        x89 = 0;
    }
    let x93;
    if x89 != 0 {
        let x90 = x3;
        let x91 = x90 == 2;
        x93 = x91 as i32;
    } else {
        x93 = 0;
    }
    // verus_assert(1);
    x93
}