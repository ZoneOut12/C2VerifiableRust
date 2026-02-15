#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32)
    requires
        n > 0,
{
    let mut x: i32 = 0;
    let mut m: i32 = 0;

    while x < n
        invariant
            x <= n,
            (n > 0) as int != 0 ==> (m >= 0) as int != 0,
            (n > 0) as int != 0 ==> (m < n) as int != 0,
            m <= x,
            0 <= x,
        decreases n - x,
    {
        if unknown() != 0 {
            m = x;
        }
        x = x + 1;
    }

    if n > 0 {
        assert(m < n);
        assert(m >= 0);
    }
}

fn valid_test_harness_foo(){
    foo(5);
    foo(3);
    foo(7);
    foo(10);
    foo(4);
    foo(1);
    foo(2);
}

fn invalid_test_harness_foo(){
    foo(0);
    foo(-2);
}

fn main() {
}

} // verus!

// RAC 
// use std::time::{SystemTime, UNIX_EPOCH};

// fn unknown() -> i32 {
//     let nanos = SystemTime::now()
//         .duration_since(UNIX_EPOCH)
//         .unwrap()
//         .subsec_nanos();
//     nanos as i32
// }

// fn foo(n: i32)
// {
//     let mut x: i32 = 0;
//     let mut m: i32 = 0;

//     while x < n
//     {
//         let old_measure = n - x;
//         assert!(
//             x <= n &&
//             (!(n > 0) || (m >= 0)) &&
//             (!(n > 0) || (m < n)) &&
//             m <= x &&
//             0 <= x
//         );
//         if unknown() != 0 {
//             m = x;
//         }
//         x = x + 1;
//         assert!(old_measure > n - x);
//     }
//     assert!(
//             x <= n &&
//             (!(n > 0) || (m >= 0)) &&
//             (!(n > 0) || (m < n)) &&
//             m <= x &&
//             0 <= x
//         );
//     if n > 0 {
//         assert!(m < n);
//         assert!(m >= 0);
//     }
// }

// fn valid_test_harness_foo(){
//     foo(5);
//     foo(3);
//     foo(7);
//     foo(10);
//     foo(4);
//     foo(1);
//     foo(2);
// }

// fn main(){
//     valid_test_harness_foo();
// }