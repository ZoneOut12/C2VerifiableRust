fn p(x0: &String) -> i32 {
    let mut x8: i32 = -1;
    let mut x9: i32 = 1;
    let mut x10: char = '\0';
    let x2: char = x0.chars().next().unwrap_or('\0');
    let x3: bool = x2 == '\0';
    let x11: &str;
    if x3 {
        x11 = x0;
    } else {
        let x4: bool = x2 >= '0';
        let x6: bool;
        if x4 {
            let x5: bool = x2 <= '9';
            x6 = x5;
        } else {
            x6 = false;
        }
        if x6 {
            x9 = 0;
            x10 = x2;
            x11 = &x0[1..];
        } else {
            x11 = x0;
        }
    }
    let x23: i32 = x9;
    if x23 != 0 {
        // char *x24 = x24;
    } else {
        let x26: char = x10;
        let x28: &str = x11;
        let x27: i8 = (x26 as u8 - '0' as u8) as i8;
        x8 = x27 as i32;
    }
    let x32: i32 = x8;
    x32
}