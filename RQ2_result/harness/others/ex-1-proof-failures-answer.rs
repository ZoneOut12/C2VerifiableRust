static mut old: i32 = 0;
static mut new: i32 = 0;

fn CheckPre_abs(x: i32)
{
    assert!(
        x>i32::MIN
    );
}

fn CheckPost_abs(x: i32, result: i32)
{
    assert!(
        (!(x>=0) || (result==x)) &&
        (!(x<0) || (result==-x))
    );
}

fn abs(x: i32) -> i32
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

fn CheckPre_distance(a: i32, b: i32)
{
    assert!(i32::MIN<b-a && b-a<=i32::MAX);
}

fn CheckPost_distance(a: i32, b: i32, result: i32)
{
    assert!(
        (!(a<b) || (a+result==b)) &&
	    (!(b<=a) || (a-result==b))
    );
}

fn distance(a: i32, b: i32) -> i32
{
    abs(b - a)
}

fn CheckPre_old_distance(a: i32, b: i32)
{
    assert!(
        (!(a<b) || (b-a<=i32::MAX)) &&
	    (!(b<=a) || (a-b<=i32::MAX))
    );
}

fn CheckPost_old_distance(a: i32, b: i32, result: i32)
{
    assert!(
        (!(a<b) || (a+result==b)) &&
	    (!(b<=a) || (a-result==b))
    );
}

fn old_distance(a: i32, b: i32) -> i32
{
    if a < b {
        b - a
    } else {
        a - b
    }
}

fn CheckPre_test(a: i32, b: i32)
{
    assert!(
        i32::MIN<b-a && b-a<=i32::MAX
    );
}

fn test(a: i32, b: i32)
 {
    unsafe {
        old = old_distance(a, b);
        new = distance(a, b);
        assert!(old==new);
    }
}


fn main(){
    valid_test_harness_test();
    valid_test_harness_abs();
    valid_test_harness_distance();
    valid_test_harness_old_distance();
    // invalid_test_harness_test();
    // invalid_test_harness_abs();
    // invalid_test_harness_distance();
    // invalid_test_harness_old_distance();
}

fn valid_test_harness_test(){
    CheckPre_test(5, 10);
    test(5, 10);

    CheckPre_test(-5, 3);
    test(-5, 3);

    CheckPre_test(-1000000, 1000000);
    test(-1000000, 1000000);

    CheckPre_test(0, 1);
    test(0, 1);

    CheckPre_test(100, -50);
    test(100, -50);

    CheckPre_test(0, -2147483647);
    test(0, -2147483647);

    CheckPre_test(0, 2147483647);
    test(0, 2147483647);
}

fn invalid_test_harness_test(){
    CheckPre_test(0, -2147483648);

    CheckPre_test(-2147483648, 2147483647);
}

fn valid_test_harness_abs() {
    // --- Test Case 1: Positive integer ---
    let x1 = 10;
    CheckPre_abs(x1);
    let res1 = 10;
    CheckPost_abs(x1, res1);

    // --- Test Case 2: Negative integer ---
    let x2 = -5;
    CheckPre_abs(x2);
    let res2 = 5;
    CheckPost_abs(x2, res2);

    // --- Test Case 3: Zero boundary ---
    let x3 = 0;
    CheckPre_abs(x3);
    let res3 = 0;
    CheckPost_abs(x3, res3);

    // --- Test Case 4: Maximum positive integer ---
    let x4 = i32::MAX;
    CheckPre_abs(x4);
    let res4 = i32::MAX;
    CheckPost_abs(x4, res4);

    // --- Test Case 5: Smallest valid negative integer ---
    let x5 = i32::MIN + 1;
    CheckPre_abs(x5);
    let res5 = i32::MAX;
    CheckPost_abs(x5, res5);

    // --- Test Case 6: Positive one ---
    let x6 = 1;
    CheckPre_abs(x6);
    let res6 = 1;
    CheckPost_abs(x6, res6);

    // --- Test Case 7: Negative one ---
    let x7 = -1;
    CheckPre_abs(x7);
    let res7 = 1;
    CheckPost_abs(x7, res7);
}

fn invalid_test_harness_abs() {
    // --- Test Case 8: Invalid - INT_MIN (Violates x > INT_MIN) ---
    // In 2's complement, -INT_MIN overflows i32
    let x8 = i32::MIN;
    CheckPre_abs(x8);

    // --- Test Case 9: Invalid - Extreme underflow ---
    let x9 = i32::MIN; 
    CheckPre_abs(x9);
}

fn valid_test_harness_distance() {
    // --- Test Case 1: a < b (Positive result) ---
    let (a1, b1) = (10, 20);
    CheckPre_distance(a1, b1);
    let res1 = 10;
    CheckPost_distance(a1, b1, res1);

    // --- Test Case 2: b < a (Positive result) ---
    let (a2, b2) = (20, 10);
    CheckPre_distance(a2, b2);
    let res2 = 10;
    CheckPost_distance(a2, b2, res2);

    // --- Test Case 3: Same values (Zero distance) ---
    let (a3, b3) = (5, 5);
    CheckPre_distance(a3, b3);
    let res3 = 0;
    CheckPost_distance(a3, b3, res3);

    // --- Test Case 4: Negative to Positive ---
    let (a4, b4) = (-5, 5);
    CheckPre_distance(a4, b4);
    let res4 = 10;
    CheckPost_distance(a4, b4, res4);

    // --- Test Case 5: Large positive range ---
    let (a5, b5) = (0, i32::MAX);
    CheckPre_distance(a5, b5);
    let res5 = i32::MAX;
    CheckPost_distance(a5, b5, res5);

    // --- Test Case 6: Small positive range ---
    let (a6, b6) = (100, 101);
    CheckPre_distance(a6, b6);
    let res6 = 1;
    CheckPost_distance(a6, b6, res6);

    // --- Test Case 7: Moving towards zero ---
    let (a7, b7) = (-10, -2);
    CheckPre_distance(a7, b7);
    let res7 = 8;
    CheckPost_distance(a7, b7, res7);
}

fn invalid_test_harness_distance() {
    // --- Test Case 8: Invalid - Result equals i32::MIN (Overflow) ---
    // Violates INT_MIN < b - a
    let (a8, b8) = (1, i32::MIN);
    CheckPre_distance(a8, b8);

    // --- Test Case 9: Invalid - Extreme spread (Violates b - a <= INT_MAX) ---
    let (a9, b9) = (i32::MAX, -10);
    CheckPre_distance(a9, b9);
}

fn valid_test_harness_old_distance() {
    // --- Test Case 1: Standard a < b ---
    let (a1, b1) = (0, 100);
    CheckPre_old_distance(a1, b1);
    let res1 = 100;
    CheckPost_old_distance(a1, b1, res1);

    // --- Test Case 2: Standard b < a ---
    let (a2, b2) = (100, 0);
    CheckPre_old_distance(a2, b2);
    let res2 = 100;
    CheckPost_old_distance(a2, b2, res2);

    // --- Test Case 3: Zero values ---
    let (a3, b3) = (0, 0);
    CheckPre_old_distance(a3, b3);
    let res3 = 0;
    CheckPost_old_distance(a3, b3, res3);

    // --- Test Case 4: Max distance a < b ---
    let (a4, b4) = (0, i32::MAX);
    CheckPre_old_distance(a4, b4);
    let res4 = i32::MAX;
    CheckPost_old_distance(a4, b4, res4);

    // --- Test Case 5: Max distance b < a ---
    let (a5, b5) = (i32::MAX, 0);
    CheckPre_old_distance(a5, b5);
    let res5 = i32::MAX;
    CheckPost_old_distance(a5, b5, res5);

    // --- Test Case 6: Negative boundary ---
    let (a6, b6) = (-1, 0);
    CheckPre_old_distance(a6, b6);
    let res6 = 1;
    CheckPost_old_distance(a6, b6, res6);

    // --- Test Case 7: Both negative ---
    let (a7, b7) = (-50, -20);
    CheckPre_old_distance(a7, b7);
    let res7 = 30;
    CheckPost_old_distance(a7, b7, res7);
}

fn invalid_test_harness_old_distance() {
    // --- Test Case 8: Invalid - Difference exceeds INT_MAX (a < b) ---
    // b - a would overflow (e.g., 0 - (-2147483648) is not representable in i32)
    let (a8, b8) = (i32::MIN, 1);
    CheckPre_old_distance(a8, b8);

    // --- Test Case 9: Invalid - Difference exceeds INT_MAX (b <= a) ---
    let (a9, b9) = (1, i32::MIN);
    CheckPre_old_distance(a9, b9);
}