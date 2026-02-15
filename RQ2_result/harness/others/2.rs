fn sum(n: char) -> i32
{
    let mut s: i32 = 0;
    let mut k: char = 0 as char;
    while k <= n
    {
        let old_measure = n as i32 - k as i32;
        assert!(
            0 <= k as i32 && k as i32 <= n as i32 + 1 &&
            s == (k as i32 - 1) * (k as i32) / 2
        );
        s = s + k as i32;
        k = char::from_u32(k as u32 + 1).unwrap();
        assert!(old_measure > n as i32 - k as i32);
    }
    assert!(
        0 <= k as i32 && k as i32 <= n as i32 + 1 &&
        s == (k as i32 - 1) * (k as i32) / 2
    );
    s
}

fn main() {
    valid_test_harness_sum();
    invalid_test_harness_sum();

    let s: i32 = sum(5 as char);
    assert!(s == 15);
}

fn CheckPre_sum(n: char)
{
    assert!(n as i32 >= 0 && n as i32 <= 100);
}

fn CheckPost_sum(n: char, s: i32)
{
    assert!(
        s >= 0,
        s == (n as i32 + 1) * (n as i32) / 2
    );
}

fn valid_test_harness_sum() {
    // Test case 1: Valid input n=1
    let n1: u8 = 1;
    CheckPre_sum(n1 as char);
    sum(n1 as char);
    let result1 = 1;
    CheckPost_sum(n1 as char, result1);

    // Test case 2: Valid input n=5
    let n2: u8 = 5;
    CheckPre_sum(n2 as char);
    sum(n2 as char);
    let result2 = 15;
    CheckPost_sum(n2 as char, result2);

    // Test case 3: Valid input n=10
    let n3: u8 = 10;
    CheckPre_sum(n3 as char);
    sum(n3 as char);
    let result3 = 55;
    CheckPost_sum(n3 as char, result3);

    // Test case 4: Valid input n=50
    let n4: u8 = 50;
    CheckPre_sum(n4 as char);
    sum(n4 as char);
    let result4 = 1275;
    CheckPost_sum(n4 as char, result4);

    // Test case 5: Valid input n=99
    let n5: u8 = 99;
    CheckPre_sum(n5 as char);
    sum(n5 as char);
    let result5 = 4950;
    CheckPost_sum(n5 as char, result5);

    // Test case 6: Boundary input n=0
    let n6: u8 = 0;
    CheckPre_sum(n6 as char);
    sum(n6 as char);
    let result6 = 0;
    CheckPost_sum(n6 as char, result6);

    // Test case 7: Boundary input n=100
    let n7: u8 = 100;
    CheckPre_sum(n7 as char);
    sum(n7 as char);
    let result7 = 5050;
    CheckPost_sum(n7 as char, result7);
}

fn invalid_test_harness_sum() {
    // Test case 8: Invalid input n=-1 (Violation: n >= 0)
    // let n8: u8 = -1;
    // CheckPre_sum(n8 as char);

    // Test case 9: Invalid input n=101 (Violation: n <= 100)
    // let n9: u8 = 101;
    // CheckPre_sum(n9 as char);
}

