fn CheckPre_simple(p: i32, n: i32, r: i32)
{
    assert!(
        p >= 5000 &&
        r > 0 && r < 15 &&
        n > 0 && n < 5 &&
        p * n * r <= i32::MAX
    );
}

fn CheckPost_simple(p: i32, n: i32, r: i32, result: i32)
{
    assert!(
        result <= 2 * p && result > 0 &&
        p * n * r <= 200 * p * n * r
    );
}

fn simple(p: i32, n: i32, r: i32) -> i32
{
    let si: i32 = p * n * r / 100;
    si
}

fn main() {
    let s: i32 = simple(10000, 3, 10);

    valid_test_harness_simple();
    // invalid_test_harness_simple();
}

fn valid_test_harness_simple() {
    // --- Test Case 1: Valid - minimum values ---
    let (p1, n1, r1) = (5000, 1, 1);
    CheckPre_simple(p1, n1, r1);
    let _res1 = simple(p1, n1, r1);

    // --- Test Case 2: Valid - original example ---
    let (p2, n2, r2) = (10000, 3, 10);
    CheckPre_simple(p2, n2, r2);
    let _res2 = simple(p2, n2, r2);

    // --- Test Case 3: Valid - mid-range values ---
    let (p3, n3, r3) = (7500, 2, 5);
    CheckPre_simple(p3, n3, r3);
    let _res3 = simple(p3, n3, r3);

    // --- Test Case 4: Boundary - max n and r ---
    let (p4, n4, r4) = (5000, 4, 14);
    CheckPre_simple(p4, n4, r4);
    let _res4 = simple(p4, n4, r4);

    // --- Test Case 5: Boundary - min n and max r ---
    let (p5, n5, r5) = (5000, 1, 14);
    CheckPre_simple(p5, n5, r5);
    let _res5 = simple(p5, n5, r5);

    // --- Test Case 8: Valid - Large p value within INT_MAX constraint ---
    let (p8, n8, r8) = (100000, 4, 14);
    CheckPre_simple(p8, n8, r8);
    let _res8 = simple(p8, n8, r8);

    // --- Test Case 9: Valid - Extreme upper boundary of n and r ---
    let (p9, n9, r9) = (5000, 4, 14);
    CheckPre_simple(p9, n9, r9);
    let _res9 = simple(p9, n9, r9);
}

fn invalid_test_harness_simple() {
    // --- Test Case 6: Invalid - p below minimum ---
    // This violates the requirement: requires p >= 5000
    let (p6, n6, r6) = (4999, 3, 10);
    CheckPre_simple(p6, n6, r6);

    // --- Test Case 7: Invalid - n at zero ---
    // This violates the requirement: requires n > 0
    let (p7, n7, r7) = (5000, 0, 5);
    CheckPre_simple(p7, n7, r7);
}