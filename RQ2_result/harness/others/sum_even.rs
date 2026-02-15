fn CheckPre_func(n: i32)
{
    assert!(
        n >= 0 &&
        n / 2 * (n / 2 + 1) <= i32::MAX
    );
}

fn CheckPost_func(n: i32, result: i32)
{
    assert!(
        result == n / 2 * (n / 2 + 1)
    ); 
}

fn func(n: i32) -> i32
{
    let mut sum: i32 = 0;
    let mut i: i32 = 0;

    while i <= n / 2
    {
        let old_measure = n / 2 - i;
        assert!(
            i <= n / 2 + 1 &&
            (sum == i * (i - 1))
        );
        sum = sum + 2 * i;
        i += 1;
        assert!(old_measure > n / 2 - i);
    }
    assert!(
        i <= n / 2 + 1 &&
        (sum == i * (i - 1))
    );
    assert!(i == n / 2 + 1);
    sum
}

fn main() {
    valid_test_harness_func();
    // invalid_test_harness_func();
}

fn valid_test_harness_func() {
    // --- Test Case 1: Minimum valid input ---
    let mut n1 = 0;
    CheckPre_func(n1);
    func(n1);

    // --- Test Case 2: Small even number ---
    let mut n2 = 4;
    CheckPre_func(n2);
    func(n2);

    // --- Test Case 3: Small odd number ---
    let mut n3 = 5;
    CheckPre_func(n3);
    func(n3);

    // --- Test Case 4: Mid-range value ---
    let mut n4 = 10;
    CheckPre_func(n4);
    func(n4);

    // --- Test Case 5: Larger even number ---
    let mut n5 = 100;
    CheckPre_func(n5);
    func(n5);

    // --- Test Case 6: Near boundary of INT_MAX ---
    let mut n6 = 92680;
    CheckPre_func(n6);
    func(n6);

    // --- Test Case 7: Another valid odd number ---
    let mut n7 = 11;
    CheckPre_func(n7);
    func(n7);
}

fn invalid_test_harness_func() {
    // --- Test Case 8: Violation - Negative n ---
    let n8 = -1;
    CheckPre_func(n8);

    // --- Test Case 9: Violation - Overflow potential ---
    let n9 = 100000;
    CheckPre_func(n9);
}
