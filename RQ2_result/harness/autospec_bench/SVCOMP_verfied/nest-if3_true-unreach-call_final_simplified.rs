#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown1() -> (result: i32) {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32, mut l: i32)
    requires
        l > 0,
        l < i32::MAX,
        n < i32::MAX,
{
    let mut k: i32;
    let mut i: i32;

    k = 1;
    while k < n
        invariant
            1 <= l,
            1 <= k,
        decreases n - k,
    {
        i = l;
        while i < n
            invariant
                1 <= i,
            decreases n - i,
        {
            assert(1 <= i);
            i += 1;
        }
        if unknown1() != 0 && l < 2147483647 {
            l = l + 1;
        }
        k += 1;
    }
}

fn valid_test_harness(){
    foo(5, 1);
    foo(10, 5);
    foo(2147483640, 2147483646);
    foo(-1, 1);
    foo(-5, 2);
    foo(1, 1);
    foo(2147483646, 2147483646);
}

fn invalid_test_harness(){
    foo(5, -5);
    foo(i32::MAX, 1);
}

fn main() {
}

} // verus!

// RAC
// fn unknown1() -> i32 {
//     kani::any()
// }

// fn foo(n: i32, mut l: i32)
// {
//     let mut k: i32;
//     let mut i: i32;

//     k = 1;
//     while k < n
//     {
//         let old_measure = n - k;
//         assert!(
//             1 <= l &&
//             1 <= k
//         );
//         i = l;
//         while i < n
//         {
//             let old_measure = n - i;
//             assert!(1 <= i);
//             assert!(1 <= i);
//             i += 1;
//             assert!(old_measure > n - i);
//         }
//         assert!(1 <= i);
//         if unknown1() != 0 && l < 2147483647 {
//             l = l + 1;
//         }
//         k += 1;
//         assert!(old_measure > n - k);
//     }
//     assert!(
//         1 <= l &&
//         1 <= k
//     );
// }

// #[kani::proof]
// fn valid_test_harness(){
//     foo(5, 1);
//     foo(10, 5);
//     foo(2147483640, 2147483646);
//     foo(-1, 1);
//     foo(-5, 2);
//     foo(1, 1);
//     foo(2147483646, 2147483646);
// }

// fn main(){}