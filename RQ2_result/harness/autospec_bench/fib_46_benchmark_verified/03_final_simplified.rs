#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32, l: i32)
    requires
        l > 0,
        n > l,
{
    let mut i: i32;
    let mut k: i32;

    k = 1;
    while k < n
        invariant
            1 <= k <= n,
        decreases n - k,
    {
        i = l;
        while i < n
            invariant
                l <= i <= n,
            decreases n - i,
        {
            i += 1;
        }

        i = l;
        while i < n
            invariant
                l <= i <= n,
            decreases n - i,
        {
            assert(1 <= i);
            i += 1;
        }

        k += 1;
    }
}

fn valid_test_harness(){
    foo(5, 2);
    foo(10, 1);
    foo(3, 1);
    foo(100, 50);
    foo(4, 1);
    foo(2, 1);
    foo(10, 9);
}

fn invalid_test_harness(){
    foo(5, 0);
    foo(2, 3);
}

fn main() {
}

} // verus!

// RAC
// fn foo(n: i32, l: i32)
// {
//     let mut i: i32;
//     let mut k: i32;

//     k = 1;
//     while k < n
//     {
//         let old_measure = n - k;
//         assert!(
//             1 <= k && k <= n
//         );
//         i = l;
//         while i < n
//         {
//             let old_measure =  n - i;
//             assert!(1 <= i && i <= n);
//             i += 1;
//             assert!(
//                 n - i < old_measure
//             );
//         }

//         i = l;
//         while i < n
//         {
//             let old_measure =  n - i;
//             assert!(1 <= i && i <= n);
//             assert!(1 <= i);
//             i += 1;
//             assert!(
//                 n - i < old_measure
//             );
//         }

//         k += 1;
//         assert!(
//             n - k < old_measure
//         );
//     }
//     assert!(
//         1 <= k && k <= n
//     );
// }

// fn valid_test_harness(){
//     foo(5, 2);
//     foo(10, 1);
//     foo(3, 1);
//     foo(100, 50);
//     foo(4, 1);
//     foo(2, 1);
//     foo(10, 9);
// }

// fn main(){
//     valid_test_harness();
// }