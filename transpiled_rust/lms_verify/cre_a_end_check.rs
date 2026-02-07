fn matcher_a_end(x0: &str) -> i32 {
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    let mut pos: usize = 0;
    while true {
        let x5: i32 = x2;
        let x9: i32;
        if x5 != 0 {
            x9 = 0;
        } else {
            x9 = x3;
        }
        if x9 == 0 {
            break;
        }
        let x11_pos: usize = pos;
        let x12: char;
        if x11_pos < x0.len() {
            x12 = x0.as_bytes()[x11_pos] as char;
        } else {
            x12 = '\u{0}';
        }
        let x13: i32 = if x12 == '\u{0}' { 1 } else { 0 };
        let x16: i32;
        if x13 != 0 {
            x16 = 0;
        } else {
            let x15: i32 = if 'a' as char == x12 { 1 } else { 0 };
            x16 = x15;
        }
        let x20: i32;
        if x16 != 0 {
            let x17_pos: usize = x11_pos + 1;
            let x18: char;
            if x17_pos < x0.len() {
                x18 = x0.as_bytes()[x17_pos] as char;
            } else {
                x18 = '\u{0}';
            }
            let x19: i32 = if x18 == '\u{0}' { 1 } else { 0 };
            x20 = x19;
        } else {
            x20 = 0;
        }
        x2 = x20;
        let x22: i32 = x2;
        if x22 != 0 {
        } else {
            let x14: i32 = if x13 != 0 { 0 } else { 1 };
            x3 = x14;
            let x25: i32 = x3;
            if x25 != 0 {
                pos = x11_pos + 1;
            }
        }
    }
    let x56: i32 = x2;
    x56
}