fn CheckPre_p(x0: &String)
{
    assert!(
        x0.len() >= 1 && 
        x0.as_bytes()[..x0.len()-1].iter().all(|&b| b != b'\0') && 
        x0.as_bytes()[x0.len()-1] == b'\0'
    );
}

fn CheckPost_p(x0: &String, result: i32)
{
    assert!(((result == -1) || ((0 <= result) && (result <= 9))));
}

fn p(x0: &String) -> i32
{
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

fn main() {
    valid_test_harness_p();
    // invalid_test_harness_p();
}

fn valid_test_harness_p() {
    // --- Test Case 1: Valid - empty string ---
    let x0_1 = String::from("\0");
    CheckPre_p(&x0_1);
    let res1 = -1;
    CheckPost_p(&x0_1, res1);

    // --- Test Case 2: Valid - single digit '5' ---
    let x0_2 = String::from("5\0");
    CheckPre_p(&x0_2);
    let res2 = 5;
    CheckPost_p(&x0_2, res2);

    // --- Test Case 3: Valid - non-digit first character ---
    let x0_3 = String::from("a\0");
    CheckPre_p(&x0_3);
    let res3 = -1;
    CheckPost_p(&x0_3, res3);

    // --- Test Case 4: Valid - digit followed by other characters ---
    let x0_4 = String::from("3xyz\0");
    CheckPre_p(&x0_4);
    let res4 = 3;
    CheckPost_p(&x0_4, res4);

    // --- Test Case 5: Valid - non-digit first character with more characters ---
    let x0_5 = String::from("X123\0");
    CheckPre_p(&x0_5);
    let res5 = -1;
    CheckPost_p(&x0_5, res5);

    // --- Test Case 6: Boundary - empty string (re-test) ---
    let x0_6 = String::from("\0");
    CheckPre_p(&x0_6);
    let res6 = -1;
    CheckPost_p(&x0_6, res6);

    // --- Test Case 7: Boundary - maximum digit '9' ---
    let x0_7 = String::from("9\0");
    CheckPre_p(&x0_7);
    let res7 = 9;
    CheckPost_p(&x0_7, res7);
}

fn invalid_test_harness_p() {
    // --- Test Case 8: Invalid - NULL reference (Simulation) ---
    // In Rust, &String cannot be null. We use unsafe to simulate the C violation.
    unsafe {
        let null_ref: &String = std::mem::transmute(std::ptr::null::<String>());
        CheckPre_p(null_ref); // This would cause an immediate crash/UB
    }

    // --- Test Case 9: Invalid - Memory safety (Simulation) ---
    let x0_9 = String::from("a");
    CheckPre_p(&x0_9);
}
