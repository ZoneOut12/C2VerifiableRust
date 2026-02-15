fn matcher_a(x0: &str) -> i32 
{
    assert!(
        x0.len() >= 1 && 
        x0.as_bytes()[..x0.len()-1].iter().all(|&b| b != b'\0') && 
        x0.as_bytes()[x0.len()-1] == b'\0'
    );
    let mut x2: i32 = 0;
    let mut x3: i32 = 1;
    // let mut x4: usize = 0;
    let mut x4: &str = &x0[..]; //0
    while true
    {
        let old_measure = x4.len() + (if x2 != 0 { 0 } else { 1 }) + (if x3 != 0 { 1 } else { 0 });
        assert!(
            x4.len() >= 1 && 
            x4.as_bytes()[..x4.len()-1].iter().all(|&b| b != b'\0') && 
            x4.as_bytes()[x4.len()-1] == b'\0'
        );
        let x5: i32 = x2;
        let x9: i32 = if x5 != 0 {
            0
        } else {
            x3
        };
        if x9 == 0 {
            break ;
        }
        // let x12: char = match x0.as_bytes().get(x4) {
        //     Some(&b) => b as char,
        //     None => '\0',
        // }; 
        // let x12 = x4.get_char(0) as char; //0
        let x12 = x4.chars().next().unwrap_or('\0');
        let x13: i32 = if x12 == '\0' {
            1
        } else {
            0
        };
        let x16: i32 = if x13 != 0 {
            0
        } else {
            if x12 == 'a' {
                1
            } else {
                0
            }
        };
        let x18: i32 = if x16 != 0 {
            1
        } else {
            0
        };
        x2 = x18;
        let x20: i32 = x2;
        if x20 != 0 {
        } else {
            let x14: i32 = if x13 == 0 {
                1
            } else {
                0
            };
            x3 = x14;
            let x23: i32 = x3;
            if x23 != 0 {
                // x4 += 1;
                // x4 = x4.substring_char(1, x4.unicode_len()); //0
                x4 = &x4[1..];
            }
        }
        assert!(old_measure > x4.len() + (if x2 != 0 { 0 } else { 1 }) + (if x3 != 0 { 1 } else { 0 }) );
    }
    assert!(
        x4.len() >= 1 && 
        x4.as_bytes()[..x4.len()-1].iter().all(|&b| b != b'\0') && 
        x4.as_bytes()[x4.len()-1] == b'\0'
    );
    x2
}

fn main() {
    valid_test_harness();
    // invalid_test_harness();
}

fn valid_test_harness() {
    let x0: &str = "abc\0";
    let result = matcher_a(x0);

    let x0: &str = "bcd\0";
    let result = matcher_a(x0);

    let x0: &str = "apple\0";
    let result = matcher_a(x0);

    let x0: &str = "zappa\0";
    let result = matcher_a(x0);

    let x0: &str = "xyz\0";
    let result = matcher_a(x0);    

    let x0: &str = "\0";
    let result = matcher_a(x0);

    let x0: &str = "a\0";
    let result = matcher_a(x0);
}

fn invalid_test_harness() {
    let x0 = "";
    let _ = matcher_a(x0);

    let x0 = "abcde";
    let _ = matcher_a(x0);
}
