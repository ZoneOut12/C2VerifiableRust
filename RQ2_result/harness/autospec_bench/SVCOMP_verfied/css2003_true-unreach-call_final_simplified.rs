#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

const LARGE_INT: i32 = 10;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(mut k: i32) -> (result: i32)
    requires
        0 <= k && k <= 1,
{
    let mut i: i32;
    let mut j: i32;
    i = 1;
    let tmp: i32 = k;
    while i < LARGE_INT
        invariant
            i == k + 2 * (i - 1) || i == k + 1 + 2 * (i - 1),
            i + k <= 2,
            1 <= i,
            1 <= i + k,
        decreases LARGE_INT - i,
    {
        i = i + 1;
        k = k - 1;
        assert(1 <= i + k && i + k <= 2 && i >= 1);
    }
    0
}

fn valid_test_harness(){
    foo(0);
    foo(1);
}

fn invalid_test_harness(){
    foo(-1);
    foo(2);
}

fn main() {
}

} // verus!

// RAC
// const LARGE_INT: i32 = 10;

// fn foo(mut k: i32) -> i32
// {
//     let mut i: i32;
//     let mut j: i32;
//     i = 1;
//     let tmp: i32 = k;
//     while i < LARGE_INT
//     {
//         let old_measuere = LARGE_INT - i;
//         assert!(
//             (i == k + 2 * (i - 1) || i == k + 1 + 2 * (i - 1)) &&
//             i + k <= 2 &&
//             1 <= i &&
//             1 <= i + k
//         );
//         i = i + 1;
//         k = k - 1;
//         assert!(1 <= i + k && i + k <= 2 && i >= 1);
//         assert!(LARGE_INT - i < old_measuere);
//     }
//     assert!(
//         (i == k + 2 * (i - 1) || i == k + 1 + 2 * (i - 1)) &&
//         i + k <= 2 &&
//         1 <= i &&
//         1 <= i + k
//     );
//     0
// }

// fn valid_test_harness(){
//     foo(0);
//     foo(1);
// }

// fn main(){
//     valid_test_harness();
// }
