fn CheckPre_dfa_aabany(input: &str)
{
    assert!(
        input.len() >= 1 && 
        input.as_bytes()[..input.len()-1].iter().all(|&b| b != b'\0') && 
        input.as_bytes()[input.len()-1] == b'\0'
    );
}

fn CheckPost_dfa_aabany(input: &str, result: i32)
{
    assert!(result == 0 || result == 1);
}

// Original translation exhibits misalignment
fn dfa_aabany(input: &str) -> i32
{
    // let chars: Vec<char> = input.chars().collect(); // misalignment
    // let len = chars.len();
    // if len == 0 {
    //     return 0;
    // }
    if input.as_bytes()[0] as char == '\0' {
        return 0;
    }
    let len: usize = input.len();
    let mut id: i32 = 0;

    // let mut index: usize = 0; // misalignment
    let mut input = input;
    // while index + 1 < len // misalignment
    while input.as_bytes()[1] as char != '\0'
    {
        let old_measure = input.len() - 1;
        assert!(
            (((input).len() - 1)) > 0 && input.len() >= (((input).len() - 1)) + 1 &&
            (id == 17 || id == 14 || id == 11 || id == 6 || id == 3 || id == 0)
        );
        // let c = chars[index]; // misalignment
        // index += 1; // misalignment
        let c = input.as_bytes()[0] as char;
        input = &input[1..];

        if id == 17 {
            let x18 = c;
            let x19 = (x18 == 'A') as i32;
            let x23: i32;
            if x19 != 0 {
                x23 = 1;
                return 1;
            } else {
                x23 = 1;
                return 1;
            }
            id = x23;
        } else if id == 14 {
            let x15 = c;
            let x16 = (x15 == 'A') as i32;
            let x24: i32;
            if x16 != 0 {
                x24 = 1;
                return 1;
            } else {
                x24 = 1;
                return 1;
            }
            id = x24;
        } else if id == 11 {
            let x12 = c;
            let x13 = (x12 == 'A') as i32;
            let x26: i32;
            if x13 != 0 {
                x26 = 1;
                return 1;
            } else {
                x26 = 1;
                return 1;
            }
            id = x26;
        } else if id == 6 {
            let x7 = c;
            let x8 = (x7 == 'A') as i32;
            if x8 != 0 {
                id = 6;
            } else {
                let x10 = (x7 == 'B') as i32;
                let x28: i32;
                if x10 != 0 {
                    x28 = 1;
                    return 1;
                } else {
                    x28 = 0;
                }
                id = x28;
            }
        } else if id == 3 {
            let x4 = c;
            let x5 = (x4 == 'A') as i32;
            let x30: i32;
            if x5 != 0 {
                x30 = 6;
            } else {
                x30 = 0;
            }
            id = x30;
        } else if id == 0 {
            let x1 = c;
            let x2 = (x1 == 'A') as i32;
            let x32: i32;
            if x2 != 0 {
                x32 = 3;
            } else {
                x32 = 0;
            }
            id = x32;
        } else {
            return -1;
        }
        assert!(old_measure > input.len() - 1);
    }
    assert!(
        (((input).len() - 1)) > 0 && input.len() >= (((input).len() - 1)) + 1 &&
        (id == 17 || id == 14 || id == 11 || id == 6 || id == 3 || id == 0)
    );
    let c = input.as_bytes()[0] as char;
    // if index < len {
        // let c = chars[index];
        if id == 17 {
            let x18 = c;
            let x19 = (x18 == 'A') as i32;
            let x23: i32;
            if x19 != 0 {
                x23 = 1;
            } else {
                x23 = 1;
            }
            id = x23;
        } else if id == 14 {
            let x15 = c;
            let x16 = (x15 == 'A') as i32;
            let x24: i32;
            if x16 != 0 {
                x24 = 1;
            } else {
                x24 = 1;
            }
            id = x24;
        } else if id == 11 {
            let x12 = c;
            let x13 = (x12 == 'A') as i32;
            let x26: i32;
            if x13 != 0 {
                x26 = 1;
            } else {
                x26 = 1;
            }
            id = x26;
        } else if id == 6 {
            let x7 = c;
            let x8 = (x7 == 'A') as i32;
            let x29: i32;
            if x8 != 0 {
                x29 = 0;
            } else {
                let x10 = (x7 == 'B') as i32;
                let x28: i32;
                if x10 != 0 {
                    x28 = 1;
                } else {
                    x28 = 0;
                }
                x29 = x28;
            }
            id = x29;
        } else if id == 3 {
            let x4 = c;
            let x5 = (x4 == 'A') as i32;
            let x30: i32;
            if x5 != 0 {
                x30 = 0;
            } else {
                x30 = 0;
            }
            id = x30;
        } else if id == 0 {
            let x1 = c;
            let x2 = (x1 == 'A') as i32;
            let x32: i32;
            if x2 != 0 {
                x32 = 0;
            } else {
                x32 = 0;
            }
            id = x32;
        } else {
            return -1;
        }
    // }
    id
}

fn main() {
    valid_test_harness_dfa_aabany();
    invalid_test_harness_dfa_aabany();
}


fn valid_test_harness_dfa_aabany() {
    // --- Test Case 1: Valid - "AAB" ---
    let input1 = "AAB\0";
    CheckPre_dfa_aabany(input1);
    let result1 = 1; // Expected: 1
    CheckPost_dfa_aabany(input1, result1);
    dfa_aabany(input1);

    // --- Test Case 2: Valid - "BAAB" ---
    let input2 = "BAAB\0";
    CheckPre_dfa_aabany(input2);
    let result2 = 1;
    CheckPost_dfa_aabany(input2, result2);
    dfa_aabany(input2);

    // --- Test Case 3: Valid - "AA" ---
    let input3 = "AA\0";
    CheckPre_dfa_aabany(input3);
    let result3 = 0; // Expected: 0
    CheckPost_dfa_aabany(input3, result3);
    dfa_aabany(input3);

    // --- Test Case 4: Valid - "AABB" ---
    let input4 = "AABB\0";
    CheckPre_dfa_aabany(input4);
    let result4 = 1;
    CheckPost_dfa_aabany(input4, result4);
    dfa_aabany(input4);

    // --- Test Case 5: Valid - "B" ---
    let input5 = "B\0";
    CheckPre_dfa_aabany(input5);
    let result5 = 0;
    CheckPost_dfa_aabany(input5, result5);
    dfa_aabany(input5);

    // --- Test Case 6: Boundary - empty string ---
    let input6 = "\0";
    CheckPre_dfa_aabany(input6);
    let result6 = 0;
    CheckPost_dfa_aabany(input6, result6);
    dfa_aabany(input6);

    // --- Test Case 7: Boundary - single character 'A' ---
    let input7 = "A\0";
    CheckPre_dfa_aabany(input7);
    let result7 = 0;
    CheckPost_dfa_aabany(input7, result7);
    dfa_aabany(input7);
}

fn invalid_test_harness_dfa_aabany() {
    // --- Test Case 8: Invalid - NULL pointer ---
    // CheckPre_dfa_aabany(None);

    // --- Test Case 9: Invalid - non-null-terminated string ---
    // Should violate strlen(input) requirement
    let str9 = "AA"; // "AA" without null terminator
    CheckPre_dfa_aabany(str9);
}