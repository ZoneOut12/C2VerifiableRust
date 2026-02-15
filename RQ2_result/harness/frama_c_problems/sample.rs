#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fun(x: i32, y: i32) -> (result: i32)
    requires
        x >= 0 && y > 0,
    ensures
        result == x / y,
{
    let mut r: i32 = x;
    let mut d: i32 = 0;

    while r >= y
        invariant
            r >= 0,
            r + d * y == x,
        decreases r - y + u128::MAX,//2D
    {
        r = r - y;
        d = d + 1;
    }
    d
}

fn CheckPre_fun(x: i32, y: i32)
    requires
        x >= 0 && y > 0,
{}

fn CheckPost_fun(x: i32, y: i32, result: i32)
    requires
        result == x / y,
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let res: i32 = fun(10, 2);
    assert(res == 5);
}

fn valid_test_harness_fun() {
    // Test case 1: Valid - normal division (10/2=5)
    let (x1, y1) = (10, 2);
    CheckPre_fun(x1, y1);
    let result1 = 5;
    CheckPost_fun(x1, y1, result1);

    // Test case 2: Valid - zero dividend (0/5=0)
    let (x2, y2) = (0, 5);
    CheckPre_fun(x2, y2);
    let result2 = 0;
    CheckPost_fun(x2, y2, result2);

    // Test case 3: Valid - dividend equals divisor (7/7=1)
    let (x3, y3) = (7, 7);
    CheckPre_fun(x3, y3);
    let result3 = 1;
    CheckPost_fun(x3, y3, result3);

    // Test case 4: Valid - multiple subtractions (15/3=5)
    let (x4, y4) = (15, 3);
    CheckPre_fun(x4, y4);
    let result4 = 5;
    CheckPost_fun(x4, y4, result4);

    // Test case 5: Valid - divisor is 1 (4/1=4)
    let (x5, y5) = (4, 1);
    CheckPre_fun(x5, y5);
    let result5 = 4;
    CheckPost_fun(x5, y5, result5);

    // Test case 8: Boundary - minimum allowed x (0/1=0)
    let (x8, y8) = (0, 1);
    CheckPre_fun(x8, y8);
    let result8 = 0;
    CheckPost_fun(x8, y8, result8);

    // Test case 9: Boundary - dividend equals divisor (5/5=1)
    let (x9, y9) = (5, 5);
    CheckPre_fun(x9, y9);
    let result9 = 1;
    CheckPost_fun(x9, y9, result9);
}

fn invalid_test_harness_fun() {
    // Test case 6: Invalid - negative dividend (-5 violates x >= 0)
    let (x6, y6) = (-5, 3);
    CheckPre_fun(x6, y6);

    // Test case 7: Invalid - zero divisor (y=0 violates y > 0)
    let (x7, y7) = (5, 0);
    CheckPre_fun(x7, y7);
}

} // verus!


// RAC
// fn fun(x: i32, y: i32) -> i32
// {
//     let mut r: i32 = x;
//     let mut d: i32 = 0;

//     while r >= y
//     {
//         let old_measure = r - y;
//         assert!(
//             r >= 0 &&
//             r + d * y == x
//         );
//         r = r - y;
//         d = d + 1;
//         assert!(old_measure > r - y);
//     }
//     assert!(
//         r >= 0 &&
//         r + d * y == x
//     );
//     d
// }


// fn main() {
//     valid_test_harness_fun();

//     let res: i32 = fun(10, 2);
//     assert!(res == 5);
// }

// fn valid_test_harness_fun() {
//     // Test case 1: Valid - normal division (10/2=5)
//     let (x1, y1) = (10, 2);
//     fun(x1, y1);

//     // Test case 2: Valid - zero dividend (0/5=0)
//     let (x2, y2) = (0, 5);
//     fun(x2, y2);

//     // Test case 3: Valid - dividend equals divisor (7/7=1)
//     let (x3, y3) = (7, 7);
//     fun(x3, y3);

//     // Test case 4: Valid - multiple subtractions (15/3=5)
//     let (x4, y4) = (15, 3);
//     fun(x4, y4);

//     // Test case 5: Valid - divisor is 1 (4/1=4)
//     let (x5, y5) = (4, 1);
//     fun(x5, y5);

//     // Test case 8: Boundary - minimum allowed x (0/1=0)
//     let (x8, y8) = (0, 1);
//     fun(x8, y8);

//     // Test case 9: Boundary - dividend equals divisor (5/5=1)
//     let (x9, y9) = (5, 5);
//     fun(x9, y9);
// }