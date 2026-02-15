fn spec_power(x: i32, n: i32) -> i32
{
    if n == 0 {
        1
    } else {
        spec_power(x, (n - 1)) * x
    }
}

fn is_power(x: i32, n: i32, m: i32) -> bool
{
    if m == spec_power(x, n) {
        true
    } else {
        false
    }
}

fn u32_spec_power(x: u32, n: u32) -> u32
{
    if n == 0 {
        1
    } else {
        u32_spec_power(x, (n - 1)) * x
    }
}

fn u32_is_power(x: u32, n: u32, m: u32) -> bool
{
    if m == u32_spec_power(x, n) {
        true
    } else {
        false
    }
}

fn CheckPre_power(x: i32, n: i32)
{
    assert!(
        0 <= n && n < i32::MAX
    );
    let m = kani::any();
    kani::assume(is_power(x, n, m));
    assert!(
        i32::MIN <= m && m <= i32::MAX
    );
}

fn CheckPost_power(x: i32, n: i32, result: i32)
{
    assert!(
        is_power(x, n, result)
    );
}

fn power(x: i32, n: i32) -> i32
{

    let mut r: i32 = 1;
    let mut i: i32 = 1;
    while i <= n
    {
        let old_measure = n - i;
        assert!(
            1 <= i && i <= n + 1 &&
            is_power(x, i - 1, r)
        );
        r *= x;
        i += 1;
        assert!(old_measure > n - i);
    }
    assert!(
        1 <= i && i <= n + 1 &&
        is_power(x, i - 1, r)
    );
    r
}

fn CheckPost_fast_power(x: u32, n: u32, result: u32)
{
    assert!(
        u32_is_power(x, n, result)
    );
}

fn fast_power(x: u32, n: u32) -> u32
{
    let n_pre: u32 = n;
    let mut r: u32 = 1;
    let mut p: u32 = x;
    let mut n: u32 = n;
    while n > 0
    {
        let old_measure = n;
        let v = kani::any();
        assert!(
            0 <= n &&
            (!u32_is_power(p, n, v) || u32_is_power(x, n_pre, r * v))
        );
        if n % 2 == 1 {
            r = r * p;
        }
        p *= p;
        n /= 2;
        assert!(old_measure > n);
    }
    let v = kani::any();
    assert!(
        0 <= n &&
        (!u32_is_power(p, n, v) || u32_is_power(x, n_pre, r * v))
    );
    assert!((u32_is_power(p, n, 1)));
    r
}


fn main() {
}

#[kani::proof]
fn valid_test_harness_power() {
    // --- Test Case 1: Valid - Positive base and exponent ---
    let (x1, n1) = (2, 3);
    CheckPre_power(x1, n1);
    let result1 = 8;
    CheckPost_power(x1, n1, result1);
    power(x1, n1);

    // --- Test Case 2: Valid - Zero base with positive exponent ---
    let (x2, n2) = (0, 5);
    CheckPre_power(x2, n2);
    let result2 = 0;
    CheckPost_power(x2, n2, result2);
    power(x2, n2);

    // --- Test Case 3: Valid - Negative base and odd exponent ---
    let (x3, n3) = (-2, 3);
    CheckPre_power(x3, n3);
    let result3 = -8;
    CheckPost_power(x3, n3, result3);
    power(x3, n3);

    // --- Test Case 4: Valid - Base 1 with large exponent ---
    let (x4, n4) = (1, i32::MAX - 1);
    CheckPre_power(x4, n4);
    let result4 = 1;
    CheckPost_power(x4, n4, result4);
    power(x4, n4);

    // --- Test Case 5: Valid - Large power within limits (2^30) ---
    let (x5, n5) = (2, 30);
    CheckPre_power(x5, n5);
    let result5 = 1073741824;
    CheckPost_power(x5, n5, result5);
    power(x5, n5);

    // --- Test Case 6: Boundary - Zero exponent (x^0 = 1) ---
    let (x6, n6) = (5, 0);
    CheckPre_power(x6, n6);
    let result6 = 1;
    CheckPost_power(x6, n6, result6);
    power(x6, n6);

    // --- Test Case 7: Boundary - -1 to an even large power ---
    let (x7, n7) = (-1, i32::MAX - 1);
    CheckPre_power(x7, n7);
    let result7 = 1;
    CheckPost_power(x7, n7, result7);
    power(x7, n7);
}

// #[kani::proof]
fn invalid_test_harness_power() {
    // --- Test Case 8: Invalid - Negative exponent ---
    // Violates: requires 0 <= n
    let (x8, n8) = (2, -1);
    CheckPre_power(x8, n8);

    // --- Test Case 9: Invalid - Overflow ---
    // Violates: requires \exists integer m; is_power(x, n, m) && INT_MIN <= m <= INT_MAX
    // 2^31 is 2147483648, which exceeds i32::MAX (2147483647)
    let (x9, n9) = (2, 31);
    CheckPre_power(x9, n9);
}

#[kani::proof]
fn valid_test_harness_fast_power() {
    // --- Test Case 1: Standard positive power (2^3) ---
    let (x1, n1) = (2, 3);
    let result1 = 8;
    CheckPost_fast_power(x1, n1, result1);

    // --- Test Case 2: Base raised to power of 0 (x^0 = 1) ---
    let (x2, n2) = (5, 0);
    let result2 = 1;
    CheckPost_fast_power(x2, n2, result2);

    // --- Test Case 3: Base of 1 (1^n = 1) ---
    let (x3, n3) = (1, 100);
    let result3 = 1;
    CheckPost_fast_power(x3, n3, result3);

    // --- Test Case 4: Base of 0 (0^n = 0 for n > 0) ---
    let (x4, n4) = (0, 5);
    let result4 = 0;
    CheckPost_fast_power(x4, n4, result4);

    // --- Test Case 5: Even exponent (Exercise squaring logic) ---
    let (x5, n5) = (3, 4);
    let result5 = 81;
    CheckPost_fast_power(x5, n5, result5);

    // --- Test Case 6: Large base, small exponent ---
    let (x6, n6) = (100, 2);
    let result6 = 10000;
    CheckPost_fast_power(x6, n6, result6);

    // --- Test Case 7: Powers of 2 (Boundary of binary representation) ---
    let (x7, n7) = (2, 10);
    let result7 = 1024;
    CheckPost_fast_power(x7, n7, result7);
}

// RAC
// fn u32_spec_power(x: u32, n: u32) -> u32
// {
//     if n == 0 {
//         1
//     } else {
//         u32_spec_power(x, (n - 1)) * x
//     }
// }

// fn u32_is_power(x: u32, n: u32, m: u32) -> bool
// {
//     if m == u32_spec_power(x, n) {
//         true
//     } else {
//         false
//     }
// }

// fn fast_power(x: u32, n: u32) -> u32
// {
//     let n_pre: u32 = n;
//     let mut r: u32 = 1;
//     let mut p: u32 = x;
//     let mut n: u32 = n;
//     while n > 0
//     {
//         if n % 2 == 1 {
//             assert!(r * u32_spec_power(p, n) == u32_spec_power(x, n_pre));
//             r = r * p;
//         }
//         p *= p;
//         n /= 2;
//     }
//     r
// }

// fn valid_test_harness_fast_power() {
//     // --- Test Case 1: Standard positive power (2^3) ---
//     let (x1, n1) = (2, 3);
//     fast_power(x1, n1);

//     // --- Test Case 2: Base raised to power of 0 (x^0 = 1) ---
//     let (x2, n2) = (5, 0);
//     fast_power(x2, n2);

//     // --- Test Case 3: Base of 1 (1^n = 1) ---
//     let (x3, n3) = (1, 100);
//     fast_power(x3, n3);

//     // --- Test Case 4: Base of 0 (0^n = 0 for n > 0) ---
//     let (x4, n4) = (0, 5);
//     fast_power(x4, n4);

//     // --- Test Case 5: Even exponent (Exercise squaring logic) ---
//     let (x5, n5) = (3, 4);
//     fast_power(x5, n5);

//     // --- Test Case 6: Large base, small exponent ---
//     let (x6, n6) = (100, 2);
//     fast_power(x6, n6);

//     // --- Test Case 7: Powers of 2 (Boundary of binary representation) ---
//     let (x7, n7) = (2, 10);
//     fast_power(x7, n7);
// }

// fn main(){
//     valid_test_harness_fast_power();
// }