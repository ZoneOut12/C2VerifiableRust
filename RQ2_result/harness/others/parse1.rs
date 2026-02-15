fn CheckPre_my_atoi(a: &String)
{
    assert!(
        a.len() >= 1 && 
        a.as_bytes()[..a.len()-1].iter().all(|&b| b != b'\0') && 
        a.as_bytes()[a.len()-1] == b'\0'
    );
}

fn CheckPost_my_atoi(a: &String, result: i32)
{
    assert!(
        0 <= result || result == -1
    );
}

fn my_atoi(a: &String) -> i32
{
    let m: i32 = (i32::MAX / 10) - 10;
    let mut r: i32 = 0;
    // let mut index: usize = 0;
    // let bytes = a.as_bytes();
    let mut s = a.as_str();

    // while index < bytes.len() && bytes[index] >= b'0' && bytes[index] <= b'9'
    while b'0' <= s.as_bytes()[0] && s.as_bytes()[0] <= b'9'
    {
        let old_measure = (s).len() - 1;
        assert!(
            (((s).len() - 1)) >= 0 && s.len() >= (((s).len() - 1)) + 1 &&
            0 <= r,
        );
        let c = s.as_bytes()[0] as char;
        if r > m {
            return -1;
        }
        r = 10 * r + (c as i32 - b'0' as i32);
        // r = 10 * r + (bytes[index] as i32 - b'0' as i32); // misalignment
        // index += 1; // misalignment
        s = &s[1..];
        assert!(old_measure > (s).len() - 1);
    }
    assert!(
        (((s).len() - 1)) >= 0 && s.len() >= (((s).len() - 1)) + 1 &&
        0 <= r,
    );
    r
}

fn main() {
    valid_test_harness_my_atoi();
    // invalid_test_harness_my_atoi();
}

fn valid_test_harness_my_atoi() {
    // --- Test Case 1: Valid input with normal number ---
    let a1 = String::from("123\0");
    CheckPre_my_atoi(&a1);
    let result1 = 123;
    CheckPost_my_atoi(&a1, result1);
    my_atoi(&a1);

    // --- Test Case 2: Valid input zero ---
    let a2 = String::from("0\0");
    CheckPre_my_atoi(&a2);
    let result2 = 0;
    CheckPost_my_atoi(&a2, result2);
    my_atoi(&a2);

    // --- Test Case 3: Valid input digits followed by non-digits ---
    let a3 = String::from("456abc\0");
    CheckPre_my_atoi(&a3);
    let result3 = 456;
    CheckPost_my_atoi(&a3, result3);
    my_atoi(&a3);

    // --- Test Case 4: Valid input leading zeros ---
    let a4 = String::from("0042\0");
    CheckPre_my_atoi(&a4);
    let result4 = 42;
    CheckPost_my_atoi(&a4, result4);
    my_atoi(&a4);

    // --- Test Case 5: Valid single digit ---
    let a5 = String::from("7\0");
    CheckPre_my_atoi(&a5);
    let result5 = 7;
    CheckPost_my_atoi(&a5, result5);
    my_atoi(&a5);

    // --- Test Case 6: Boundary empty string ---
    let a6 = String::from("\0");
    CheckPre_my_atoi(&a6);
    let result6 = 0; // Loop does not run, initial r is 0
    CheckPost_my_atoi(&a6, result6);
    my_atoi(&a6);

    // --- Test Case 7: Boundary input at overflow threshold ---
    // m = (2147483647 / 10) - 10 = 214748364 - 10 = 214748354
    let a7 = String::from("214748354\0");
    CheckPre_my_atoi(&a7);
    let result7 = 214748354;
    CheckPost_my_atoi(&a7, result7);
    my_atoi(&a7);
}

fn invalid_test_harness_my_atoi() {
    // --- Test Case 8: Invalid NULL pointer simulation ---
    // In Rust, references cannot be null. This is for simulation only.
    unsafe {
        let null_ref: &String = std::mem::transmute(std::ptr::null::<String>());
        CheckPre_my_atoi(null_ref);
    }

    // --- Test Case 9: Invalid non-null-terminated array simulation ---
    let a9 = String::from("12");
    CheckPre_my_atoi(&a9);
}