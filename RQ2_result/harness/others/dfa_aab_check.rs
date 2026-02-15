fn CheckPre_dfa_aab(input: &str)
{
    assert!(
        input.len() >= 1 && 
        input.as_bytes()[..input.len()-1].iter().all(|&b| b != b'\0') && 
        input.as_bytes()[input.len()-1] == b'\0'
    );
}

fn CheckPost_dfa_aab(input: &str, result: i32)
{
    assert!(
        result == 0 || result == 1
    );
}

// Original translation exhibits misalignment
fn dfa_aab(input: &str) -> i32
{
    // if input.is_empty() { // misalignment
    if input.as_bytes()[0] as char == '\0' {
        return 0;
    }
    let mut id: i32 = 0;
    let len: usize = input.len();
    // let mut pos: usize = 0;
    let mut input = input;

    // while pos + 1 < len
    while input.as_bytes()[1] as char != '\0' // misalignment
    {
        let old_measure = input.len() - 1;
        assert!(
            ((((input).len() - 1)) > 0 && input.len() >= (((input).len() - 1)) + 1 ) &&
            (id == 6 || id == 3 || id == 0)
        );
        let c = input.as_bytes()[0] as char;
        input = &input[1..];
        // let c: char = input.as_bytes()[pos] as char; // misalignment
        if id == 0 {
            let x1: char = c;
            let x2: i32 = if x1 == 'A' {
                1
            } else {
                0
            };
            let x16: i32;
            if x2 != 0 {
                x16 = 3;
            } else {
                x16 = 0;
            }
            id = x16;
        } else if id == 6 {
            let x7: char = c;
            let x8: i32 = if x7 == 'A' {
                1
            } else {
                0
            };
            let x13: i32;
            if x8 != 0 {
                x13 = 6;
            } else {
                x13 = 0;
            }
            id = x13;
        } else if id == 3 {
            let x4: char = c;
            let x5: i32 = if x4 == 'A' {
                1
            } else {
                0
            };
            let x14: i32;
            if x5 != 0 {
                x14 = 6;
            } else {
                x14 = 0;
            }
            id = x14;
        } else {
            return -1;
        }
        // pos += 1; // misalignment
        assert!(old_measure > input.len() - 1);
    }
    assert!(
        ((((input).len() - 1)) > 0 && input.len() >= (((input).len() - 1)) + 1 )&&
        (id == 6 || id == 3 || id == 0)
    );

    // if pos < len { // misalignment
    if (input.as_bytes()[0] as char != '\0') {
        // let c: char = input.as_bytes()[pos] as char; // misalignment
        let c = input.as_bytes()[0] as char;
        if id == 0 {
            let x1: char = c;
            let x2: i32 = if x1 == 'A' {
                1
            } else {
                0
            };
            let x16: i32;
            if x2 != 0 {
                x16 = 0;
            } else {
                x16 = 0;
            }
            id = x16;
        } else if id == 6 {
            let x7: char = c;
            let x8: i32 = if x7 == 'A' {
                1
            } else {
                0
            };
            let x13: i32;
            if x8 != 0 {
                x13 = 0;
            } else {
                x13 = 1;
            }
            id = x13;
        } else if id == 3 {
            let x4: char = c;
            let x5: i32 = if x4 == 'A' {
                1
            } else {
                0
            };
            let x14: i32;
            if x5 != 0 {
                x14 = 0;
            } else {
                x14 = 0;
            }
            id = x14;
        } else {
            return -1;
        }
    }
    id
}

fn main() {
    valid_test_harness_dfa_aab();
    invalid_test_harness_dfa_aab();
}

fn valid_test_harness_dfa_aab() {
    // --- Test Case 1: Valid - input "AAB" ---
    let str1 = "AAB\0";
    CheckPre_dfa_aab(str1);
    let result1 = 1; // Expected: 1 (true)
    CheckPost_dfa_aab(str1, result1);
    dfa_aab(str1);

    // --- Test Case 2: Valid - input "AAAAB" ---
    let str2 = "AAAAB\0";
    CheckPre_dfa_aab(str2);
    let result2 = 1;
    CheckPost_dfa_aab(str2, result2);
    dfa_aab(str2);

    // --- Test Case 3: Valid - input "A" ---
    let str3 = "A\0";
    CheckPre_dfa_aab(str3);
    let result3 = 0; // Expected: 0 (false)
    CheckPost_dfa_aab(str3, result3);
    dfa_aab(str3);

    // --- Test Case 4: Valid - input "B" ---
    let str4 = "B\0";
    CheckPre_dfa_aab(str4);
    let result4 = 0;
    CheckPost_dfa_aab(str4, result4);
    dfa_aab(str4);

    // --- Test Case 5: Valid - input "AA" ---
    let str5 = "AA\0";
    CheckPre_dfa_aab(str5);
    let result5 = 0;
    CheckPost_dfa_aab(str5, result5);
    dfa_aab(str5);

    // --- Test Case 6: Boundary - empty string ---
    let str6 = "\0";
    CheckPre_dfa_aab(str6);
    let result6 = 0;
    CheckPost_dfa_aab(str6, result6);
    dfa_aab(str6);

    // --- Test Case 7: Boundary - input "AB" ---
    let str7 = "AB\0";
    CheckPre_dfa_aab(str7);
    let result7 = 0;
    CheckPost_dfa_aab(str7, result7);
    dfa_aab(str7);
}

fn invalid_test_harness_dfa_aab() {
    // --- Test Case 8: Invalid - NULL pointer ---
    // Violates \valid(input)
    // CheckPre_dfa_aab(None);

    // --- Test Case 9: Invalid - non-null-terminated array ---
    // Violates strlen(input) requirement
    let str9 = "AB";
    CheckPre_dfa_aab(str9);
}