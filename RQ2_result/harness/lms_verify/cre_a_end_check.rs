fn matcher_a_end(x0: &str) -> i32 
{
    assert!(
        x0.len() >= 1 && 
        x0.as_bytes()[..x0.len()-1].iter().all(|&b| b != b'\0') && 
        x0.as_bytes()[x0.len()-1] == b'\0'
    );
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    // let mut pos: usize = 0;
    // let mut x4: &str = x0.substring_char(0, x0.unicode_len()); //0
    let mut x4: &str = &x0[..];
    while true
    {
        let old_measure = x4.len() + (if x2 != 0 { 0 } else { 1 }) + (if x3 != 0 { 1 } else { 0 });
        assert!(
            x4.len() >= 1 && 
            x4.as_bytes()[..x4.len()-1].iter().all(|&b| b != b'\0') && 
            x4.as_bytes()[x4.len()-1] == b'\0'
        );
        let x5: i32 = x2;
        let x9: i32;
        if x5 != 0 {
            x9 = 0;
        } else {
            x9 = x3;
        }
        if x9 == 0 {
            break ;
        }
        // let x11_pos: usize = pos;
        // let x12: char;
        // if x11_pos < x0.len() {
        //     x12 = x0.as_bytes()[x11_pos] as char;
        // } else {
        //     x12 = '\u{0}';
        // }
        // let x12 = x4.get_char(0) as char; //0
        let x12 = x4.chars().next().unwrap_or('\0');
        let x13: i32 = if x12 == '\u{0}' {
            1
        } else {
            0
        };
        let x16: i32;
        if x13 != 0 {
            x16 = 0;
        } else {
            let x15: i32 = if 'a' as char == x12 {
                1
            } else {
                0
            };
            x16 = x15;
        }
        let x20: i32;
        if x16 != 0 {
            // let x17_pos: usize = x11_pos + 1;
            // let x18: char;
            // if x17_pos < x0.len() {
            //     x18 = x0.as_bytes()[x17_pos] as char;
            // } else {
            //     x18 = '\u{0}';
            // }
            // let x17 = x4.substring_char(1, x4.unicode_len()); //0
            let x17: &str = &x4[1..];
            // let x18 = x17.get_char(0) as char; //0
            let x18 = x17.chars().next().unwrap_or('\0');
            let x19: i32 = if x18 == '\u{0}' {
                1
            } else {
                0
            };
            x20 = x19;
        } else {
            x20 = 0;
        }
        x2 = x20;
        let x22: i32 = x2;
        if x22 != 0 {
        } else {
            let x14: i32 = if x13 != 0 {
                0
            } else {
                1
            };
            x3 = x14;
            let x25: i32 = x3;
            if x25 != 0 {
                // pos = x11_pos + 1;
                // x4 = x4.substring_char(1, x4.unicode_len()); //0
                x4 = &x4[1..];
            }
        }
        assert!( old_measure > ((((x4).len()) + (if (x2!=0) { 0 } else {
                    1
                })) + (if (x3!=0) {
                    1
                } else { 
                    0
                })));
    }
    assert!(
        x4.len() >= 1 && 
        x4.as_bytes()[..x4.len()-1].iter().all(|&b| b != b'\0') && 
        x4.as_bytes()[x4.len()-1] == b'\0'
    );
    let x56: i32 = x2;
    x56
}

fn main() {
    valid_test_harness();
    // invalid_test_harness();
}

fn valid_test_harness(){
    let s: &str = "ba\0";
    let r = matcher_a_end(s);

    let s: &str = "testa\0";
    let r = matcher_a_end(s);

    let s: &str = "aaaa\0";
    let r = matcher_a_end(s);

    let s: &str = "abc\0";
    let r = matcher_a_end(s);

    let s: &str = "hello\0";
    let r = matcher_a_end(s);

    let s: &str = "\0";
    let r = matcher_a_end(s);

    let s: &str = "a\0";
    let r = matcher_a_end(s);
}

fn invalid_test_harness() {
    let x0 = "";
    let _ = matcher_a_end(x0);

    let x0 = "x";
    let _ = matcher_a_end(x0);
}