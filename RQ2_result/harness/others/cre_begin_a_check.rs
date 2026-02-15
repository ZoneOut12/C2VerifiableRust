fn CheckPre_matcher_begin_a(x0: &String)
{
    assert!(
        x0.len() >= 1 && 
        x0.as_bytes()[..x0.len()-1].iter().all(|&b| b != b'\0') && 
        x0.as_bytes()[x0.len()-1] == b'\0'
    );
}

fn matcher_begin_a(x0: &String) -> i32
{
    let x2: char = x0.chars().next().unwrap_or('\0');
    let x3: i32 = if x2 == '\0' {
        1
    } else {
        0
    };
    let x6: i32;
    if x3 != 0 {
        x6 = 0;
    } else {
        let x5: i32 = if 'a' == x2 {
            1
        } else {
            0
        };
        x6 = x5;
    }
    let x8: i32 = if x6 != 0 {
        1
    } else {
        0
    };
    x8
}

fn main() {
    valid_test_harness_matcher_begin_a();
    invalid_test_harness_matcher_begin_a();
}

fn valid_test_harness_matcher_begin_a() {
    // --- Test Case 1: Valid - starts with 'a' ---
    let str1 = &"a\0".to_string();
    CheckPre_matcher_begin_a(str1);

    // --- Test Case 2: Valid - starts with 'a' (multi-character) ---
    let str2 = &"apple\0".to_string();
    CheckPre_matcher_begin_a(str2);

    // --- Test Case 3: Valid - starts with 'b' ---
    let str3 = &"b\0".to_string();
    CheckPre_matcher_begin_a(str3);

    // --- Test Case 4: Valid - starts with 'x' (multi-character) ---
    let str4 = &"xyz\0".to_string();
    CheckPre_matcher_begin_a(str4);

    // --- Test Case 5: Valid - starts with 'h' ---
    let str5 = &"hello\0".to_string();
    CheckPre_matcher_begin_a(str5);

    // --- Test Case 6: Boundary - empty string ---
    let str6 = &"\0".to_string();
    CheckPre_matcher_begin_a(str6);

    // --- Test Case 7: Boundary - single character 'a' ---
    let str7 = &"a\0".to_string();
    CheckPre_matcher_begin_a(str7);
}

fn invalid_test_harness_matcher_begin_a() {
    // --- Test Case 8: Invalid - NULL pointer (Violates \valid) ---
    // CheckPre_matcher_begin_a(None);

    // --- Test Case 9: Invalid - non-terminated array (Violates strlen requirement) ---
    let str9 = &"ab".to_string();
    CheckPre_matcher_begin_a(str9);
}