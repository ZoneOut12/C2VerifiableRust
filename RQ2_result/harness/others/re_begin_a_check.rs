fn CheckPre_matcher(x0: &String)
{
    assert!(
        x0.len() >= 1 && 
        x0.as_bytes()[..x0.len()-1].iter().all(|&b| b != b'\0') && 
        x0.as_bytes()[x0.len()-1] == b'\0'
    );
}

fn matcher(x0: &String) -> i32
{
    let x2: i32 = x0.len() as i32;
    let x3: i32 = (0 < x2) as i32;
    let x6: i32;
    if x3 != 0 {
        let x4: u8 = x0.as_bytes()[0];
        let x5: i32 = (x4 == b'a') as i32;
        x6 = x5;
    } else {
        x6 = 0;
    }
    let x7: i32;
    if x6 != 0 {
        x7 = 1;
    } else {
        x7 = 0;
    }
    x7
}

fn main() {
    valid_test_harness_matcher();
    // invalid_test_harness_matcher();
}

fn valid_test_harness_matcher() {
    // --- Test Case 1: Valid string starting with 'a' ---
    let x0_1 = String::from("apple\0");
    CheckPre_matcher(&x0_1);

    // --- Test Case 2: Valid string not starting with 'a' ---
    let x0_2 = String::from("banana\0");
    CheckPre_matcher(&x0_2);

    // --- Test Case 3: Valid string with mixed characters ---
    let x0_3 = String::from("test123\0");
    CheckPre_matcher(&x0_3);

    // --- Test Case 4: Valid string starting with 'a' ---
    let x0_4 = String::from("another\0");
    CheckPre_matcher(&x0_4);

    // --- Test Case 5: Valid string not starting with 'a' ---
    let x0_5 = String::from("xyz\0");
    CheckPre_matcher(&x0_5);

    // --- Test Case 6: Boundary - empty string ---
    let x0_6 = String::from("\0");
    CheckPre_matcher(&x0_6);

    // --- Test Case 7: Boundary - single 'a' character ---
    let x0_7 = String::from("a\0");
    CheckPre_matcher(&x0_7);
}

fn invalid_test_harness_matcher() {
    // --- Test Case 8: Invalid - NULL pointer simulation ---
    // In Rust, references cannot be null. This simulates a C-style failure.
    unsafe {
        let null_ref: &String = std::mem::transmute(std::ptr::null::<String>());
        CheckPre_matcher(null_ref); 
    }

    // --- Test Case 9: Invalid - non-null-terminated array
    let x0_9 = String::from("xy");
    CheckPre_matcher(&x0_9);

}