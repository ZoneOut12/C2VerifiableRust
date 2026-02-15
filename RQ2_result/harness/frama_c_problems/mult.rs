// #[allow(unused_imports)]
// use vstd::math::*;
// use vstd::prelude::*;
// use vstd::slice::*;
// verus! {

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn mul(a: i32, b: i32) -> (result: i32)
//     requires
//         a >= 0 && b >= 0,
//         a * b <= i32::MAX,
//     ensures
//         result == a * b,
// {
//     let mut x: i32 = a;
//     let mut prod: i32 = 0;
//     while x > 0
//         invariant
//             x >= 0,
//             prod == (a - x) * b,
//         decreases x,
//     {
//         assert(x >= 1 && prod == (a - x) * b);
//         assert(prod <= a * b - b);
//         prod = prod + b;
//         x -= 1;
//     }
//     prod
// }

// fn CheckPre_mul(a: i32, b: i32)
//     requires
//         a >= 0 && b >= 0,
//         a * b <= i32::MAX,
// {}

// fn CheckPost_mul(a: i32, b: i32, result: i32)
//     requires
//         result == a * b,
// {}

// #[verifier::loop_isolation(false)]
// #[verifier::exec_allows_no_decreases_clause]
// fn main() {
//     let pdt: i32 = mul(2, 5);
//     assert(pdt == 10);
// }

// fn valid_test_harness_mul() {
//     // Test case 1: Valid - normal case
//     let a1 = 2; let b1 = 5;
//     CheckPre_mul(a1, b1);
//     let result1 = 10;
//     CheckPost_mul(a1, b1, result1);

//     // Test case 2: Valid - zero first parameter
//     let a2 = 0; let b2 = 5;
//     CheckPre_mul(a2, b2);
//     let result2 = 0;
//     CheckPost_mul(a2, b2, result2);

//     // Test case 3: Valid - zero second parameter
//     let a3 = 5; let b3 = 0;
//     CheckPre_mul(a3, b3);
//     let result3 = 0;
//     CheckPost_mul(a3, b3, result3);

//     // Test case 4: Valid - larger values
//     let a4 = 10; let b4 = 100;
//     CheckPre_mul(a4, b4);
//     let result4 = 1000;
//     CheckPost_mul(a4, b4, result4);

//     // Test case 5: Valid - product equals i32::MAX
//     let a5 = 1; let b5 = i32::MAX;
//     CheckPre_mul(a5, b5);
//     let result5 = i32::MAX;
//     CheckPost_mul(a5, b5, result5);

//     // Test case 8: Boundary - both zeros
//     let a8 = 0; let b8 = 0;
//     CheckPre_mul(a8, b8);
//     let result8 = 0;
//     CheckPost_mul(a8, b8, result8);

//     // Test case 9: Boundary - product at maximum
//     let a9 = i32::MAX; let b9 = 1;
//     CheckPre_mul(a9, b9);
//     let result9 = i32::MAX;
//     CheckPost_mul(a9, b9, result9);
// }

// fn invalid_test_harness_mul() {
//     // Test case 6: Invalid - negative first parameter (Violation: a >= 0)
//     CheckPre_mul(-1, 5);

//     // Test case 7: Invalid - product exceeds i32::MAX (Violation: a * b <= INT_MAX)
//     CheckPre_mul(1073741824, 2);
// }

// } // verus!

// RAC
fn mul(a: i32, b: i32) -> i32
{
    let mut x: i32 = a;
    let mut prod: i32 = 0;
    while x > 0
    {
        let old_measure = x;
        assert!(
            x >= 0 &&
            prod == (a - x) * b
        );
        assert!(x >= 1 && prod == (a - x) * b);
        assert!(prod <= a * b - b);
        prod = prod + b;
        x -= 1;
        assert!(old_measure > x);
    }
    assert!(
        x >= 0 &&
        prod == (a - x) * b
    );
    prod
}

fn main() {
    valid_test_harness_mul();
    
    let pdt: i32 = mul(2, 5);
    assert!(pdt == 10);
}

fn valid_test_harness_mul() {
    // Test case 1: Valid - normal case
    let a1 = 2; let b1 = 5;
    mul(a1, b1);

    // Test case 2: Valid - zero first parameter
    let a2 = 0; let b2 = 5;
    mul(a2, b2);

    // Test case 3: Valid - zero second parameter
    let a3 = 5; let b3 = 0;
    mul(a3, b3);

    // Test case 4: Valid - larger values
    let a4 = 10; let b4 = 100;
    mul(a4, b4);

    // Test case 5: Valid - product equals i32::MAX
    let a5 = 1; let b5 = i32::MAX;
    mul(a5, b5);

    // Test case 8: Boundary - both zeros
    let a8 = 0; let b8 = 0;
    mul(a8, b8);

    // Test case 9: Boundary - product at maximum
    let a9 = i32::MAX; let b9 = 1;
    mul(a9, b9);
}
