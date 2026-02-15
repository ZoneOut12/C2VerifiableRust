fn matcher_ab_dot_star_ab(x0: &str) -> i32 
{
    assert!(
        x0.len() >= 1 && 
        x0.as_bytes()[..x0.len()-1].iter().all(|&b| b != b'\0') && 
        x0.as_bytes()[x0.len()-1] == b'\0'
    );
    // let bytes = x0.as_bytes();
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    // let mut x4: usize = 0;
    // let mut x4: &str = x0.substring_char(0, x0.unicode_len()); //0
    let mut x4: &str = &x0[..];
    loop
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
            let x7: i32 = x3;
            x9 = x7;
        }
        if x9 == 0 {
            break ;
        }
        let x12: u8;
        // if x4 < bytes.len() {
            // x12 = bytes[x4];
        // } else {
            // x12 = 0;
        // }
        // let x12 = x4.get_char(0); //0
        let x12 = x4.chars().next().unwrap_or('\0');
        let x13: i32 = if x12 == '\0' { //0
            1
        } else {
            0
        };
        let x16: i32;
        if x13 != 0 {
            x16 = 0;
        } else {
            let x15: i32 = if x12 == 'a' { //0
                1
            } else {
                0
            };
            x16 = x15;
        }
        let x88: i32;
        if x16 != 0 {
            // let x17: usize = x4 + 1;
            // let x18: u8;
            // if x17 < bytes.len() {
                // x18 = bytes[x17];
            // } else {
                // x18 = 0;
            // }
            // let x17 = x4.substring_char(1, x4.unicode_len()); //0
            let x17: &str = &x4[1..];
            // let x18 = x17.get_char(0); //0
            let x18 = x17.chars().next().unwrap_or('\0');
            let x19: i32 = if x18 == '\0' { //0
                1
            } else {
                0
            };
            let x22: i32;
            if x19 != 0 {
                x22 = 0;
            } else {
                let x21: i32 = if x18 == 'b' { //0
                    1
                } else {
                    0
                };
                x22 = x21;
            }
            let x87: i32;
            if x22 != 0 {
                // let x23: usize = x17 + 1;
                // let mut x26: usize = x23;
                // let mut x26 = x17.substring_char(1, x17.unicode_len()); //0
                let mut x26: &str = &x17[1..];
                let mut x24: i32 = 0;
                let mut x25: i32 = 1;
                loop
                {
                    let old_measure = x26.len() + (if x24 != 0 { 0 } else { 1 }) + (if x25 != 0 { 1 } else { 0 });
                    assert!(
                        x26.len() >= 1 && 
                        x26.as_bytes()[..x26.len()-1].iter().all(|&b| b != b'\0') && 
                        x26.as_bytes()[x26.len()-1] == b'\0'
                    );
                    let x27: i32 = x24;
                    let x31: i32;
                    if x27 != 0 {
                        x31 = 0;
                    } else {
                        let x29: i32 = x25;
                        x31 = x29;
                    }
                    if x31 == 0 {
                        break ;
                    }
                    // let x33: usize = x26;
                    // let x34: u8;
                    // if x33 < bytes.len() {
                        // x34 = bytes[x33];
                    // } else {
                        // x34 = 0;
                    // }
                    // let x33 = x26.substring_char(0, x26.unicode_len()); //0
                    let x33: &str = &x26[..];
                    // let x34 = x33.get_char(0); //0
                    let x34 = x33.chars().next().unwrap_or('\0');
                    let x35: i32 = if x34 == '\0' { //0
                        1
                    } else {
                        0
                    };
                    let x38: i32;
                    if x35 != 0 {
                        x38 = 0;
                    } else {
                        let x37: i32 = if x34 == 'a' { //0
                            1
                        } else {
                            0
                        };
                        x38 = x37;
                    }
                    let x47: i32;
                    if x38 != 0 {
                        // let x39: usize = x33 + 1;
                        // let x40: u8;
                        // if x39 < bytes.len() {
                            // x40 = bytes[x39];
                        // } else {
                            // x40 = 0;
                        // }
                        // let x39 = x33.substring_char(1, x33.unicode_len()); //0
                        let x39: &str = &x33[1..];
                        // let x40 = x39.get_char(0); //0
                        let x40 = x39.chars().next().unwrap_or('\0');
                        let x41: i32 = if x40 == '\0' { //0
                            1
                        } else {
                            0
                        };
                        let x44: i32;
                        if x41 != 0 {
                            x44 = 0;
                        } else {
                            let x43: i32 = if x40 == 'b' { //0
                                1
                            } else {
                                0
                            };
                            x44 = x43;
                        }
                        let x46: i32 = if x44 != 0 {
                            1
                        } else {
                            0
                        };
                        x47 = x46;
                    } else {
                        x47 = 0;
                    }
                    x24 = x47;
                    let x49: i32 = x24;
                    if x49 != 0 {
                    } else {
                        let x36: i32 = if x35 != 0 {
                            0
                        } else {
                            1
                        };
                        x25 = x36;
                        let x52: i32 = x25;
                        if x52 != 0 {
                            x25 = 1;
                            // let x39: usize = x33 + 1;
                            // let x39 = x33.substring_char(1, x33.unicode_len()); //0
                            let x39: &str = &x33[1..];
                            x26 = x39;
                        }
                    }
                    assert!(old_measure > x26.len() + (if x24 != 0 { 0 } else { 1 }) + (if x25 != 0 { 1 } else { 0 }) );
                }
                assert!(
                    x26.len() >= 1 && 
                    x26.as_bytes()[..x26.len()-1].iter().all(|&b| b != b'\0') && 
                    x26.as_bytes()[x26.len()-1] == b'\0'
                );
                x87 = x24;
            } else {
                x87 = 0;
            }
            x88 = x87;
        } else {
            x88 = 0;
        }
        x2 = x88;
        let x90: i32 = x2;
        if x90 != 0 {
        } else {
            let x14: i32 = if x13 != 0 {
                0
            } else {
                1
            };
            x3 = x14;
            let x93: i32 = x3;
            if x93 != 0 {
                // let x17: usize = x4 + 1;
                // x4 = x17;
                // let x17 = x4.substring_char(1, x4.unicode_len()); //0
                let x17: &str = &x4[1..];
                x4 = x17;
            }
        }
        assert!(old_measure > x4.len() + (if x2 != 0 { 0 } else { 1 }) + (if x3 != 0 { 1 } else { 0 }) );
    }
    assert!(
        x4.len() >= 1 && 
        x4.as_bytes()[..x4.len()-1].iter().all(|&b| b != b'\0') && 
        x4.as_bytes()[x4.len()-1] == b'\0'
    );
    let x124: i32 = x2;
    x124
}

fn main() {
    valid_test_harness();
    // invalid_test_harness();
}

fn valid_test_harness(){
    let x0: &str = "abab\0";
    let result = matcher_ab_dot_star_ab(x0);

    let x0: &str = "abxab\0";
    let result = matcher_ab_dot_star_ab(x0);

    let x0: &str = "ab123ab\0";
    let result = matcher_ab_dot_star_ab(x0);

    let x0: &str = "aab\0";
    let result = matcher_ab_dot_star_ab(x0);

    let x0: &str = "ab\0";
    let result = matcher_ab_dot_star_ab(x0);

    let x0: &str = "\0";
    let result = matcher_ab_dot_star_ab(x0);

    let x0: &str = "a\0";
    let result = matcher_ab_dot_star_ab(x0);
}

fn invalid_test_harness(){
    let x0: &str = "";
    let _ = matcher_ab_dot_star_ab(x0);

    let x0: &str = "ab";
    let _ = matcher_ab_dot_star_ab(x0);
}

