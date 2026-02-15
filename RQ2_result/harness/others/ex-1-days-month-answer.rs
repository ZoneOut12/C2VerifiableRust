fn CheckPost_leap(y: i32, result: i32)
{
    assert!(
        !((result) != 0) || (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0))
    );
}

fn leap(y: i32) -> i32
{
    (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0)) as i32
}

fn CheckPre_day_of(m: i32, y: i32)
{
    assert!(1 <= m && m <= 12);
}

fn CheckPost_day_of(m: i32, y: i32, result: i32)
{
    assert!(
        (!(([2].contains(&m)) && (((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0))) || (result
            == 29)) &&
        (!(([2].contains(&m)) && ((!(((((y % 4 == 0) && (y % 100 != 0)) || (y % 400 == 0)))
            )))) || (result == 28)) &&
        (!([4,6,9,11].contains(&m)) || (result == 30)) &&
        (!([1,3,5,7,8,10,12].contains(&m)) || (result == 31))
    );
}

fn day_of(m: i32, y: i32) -> i32
{
    let days: [i32; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    let n: i32 = days[(m - 1) as usize];
    if n == 28 {
        if leap(y) != 0 {
            return 29;
        } else {
            return 28;
        }
    }
    return n;
}

fn main() {
    valid_test_harness_leap();
    valid_test_harness_day_of();
    // invalid_test_harness_day_of();
}

fn valid_test_harness_leap() {
    // --- Test Case L1: Leap year (divisible by 4, not 100) ---
    let y_l1 = 2024;
    let result_l1 = 1; 
    CheckPost_leap(y_l1, result_l1);

    // --- Test Case L2: Leap year (divisible by 400) ---
    let y_l2 = 2000;
    let result_l2 = 1;
    CheckPost_leap(y_l2, result_l2);

    // --- Test Case L3: Non-leap year (divisible by 100, not 400) ---
    let y_l3 = 1900;
    let result_l3 = 0;
    CheckPost_leap(y_l3, result_l3);

    // --- Test Case L4: Non-leap year (not divisible by 4) ---
    let y_l4 = 2023;
    let result_l4 = 0;
    CheckPost_leap(y_l4, result_l4);

    // --- Test Case L5: Boundary - Year 1 (Minimum positive year) ---
    let y_l5 = 1;
    let result_l5 = 0;
    CheckPost_leap(y_l5, result_l5);

    // --- Test Case L6: Even year not divisible by 4 (Non-leap) ---
    let y_l6 = 2022;
    let result_l6 = 0;
    CheckPost_leap(y_l6, result_l6);

    // --- Test Case L7: Large leap year (Divisible by 400) ---
    let y_l7 = 2400;
    let result_l7 = 1;
    CheckPost_leap(y_l7, result_l7);
}

fn valid_test_harness_day_of() {
    // --- Test Case 1: Valid - February in leap year ---
    let (m1, y1) = (2, 2000);
    CheckPre_day_of(m1, y1);
    let result1 = 29;
    CheckPost_day_of(m1, y1, result1);

    // --- Test Case 2: Valid - February in non-leap year ---
    let (m2, y2) = (2, 1900);
    CheckPre_day_of(m2, y2);
    let result2 = 28;
    CheckPost_day_of(m2, y2, result2);

    // --- Test Case 3: Valid - April (30 days) ---
    let (m3, y3) = (4, 2021);
    CheckPre_day_of(m3, y3);
    let result3 = 30;
    CheckPost_day_of(m3, y3, result3);

    // --- Test Case 4: Valid - May (31 days) ---
    let (m4, y4) = (5, 2022);
    CheckPre_day_of(m4, y4);
    let result4 = 31;
    CheckPost_day_of(m4, y4, result4);

    // --- Test Case 5: Valid - August (31 days) ---
    let (m5, y5) = (8, 2023);
    CheckPre_day_of(m5, y5);
    let result5 = 31;
    CheckPost_day_of(m5, y5, result5);

    // --- Test Case 8: Boundary - January (minimum month) ---
    let (m8, y8) = (1, 2024);
    CheckPre_day_of(m8, y8);
    let result8 = 31;
    CheckPost_day_of(m8, y8, result8);

    // --- Test Case 9: Boundary - December (maximum month) ---
    let (m9, y9) = (12, 2024);
    CheckPre_day_of(m9, y9);
    let result9 = 31;
    CheckPost_day_of(m9, y9, result9);
}

fn invalid_test_harness_day_of() {
    // --- Test Case 6: Invalid - month less than 1 ---
    // Violates requires 1 <= m
    let (m6, y6) = (0, 2020);
    CheckPre_day_of(m6, y6);

    // --- Test Case 7: Invalid - month greater than 12 ---
    // Violates requires m <= 12
    let (m7, y7) = (13, 2020);
    CheckPre_day_of(m7, y7);
}