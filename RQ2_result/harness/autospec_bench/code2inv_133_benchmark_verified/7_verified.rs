#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

#[verifier::external_body]
#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(mut x: i32, mut y: i32)
    requires
        0 <= x <= 10,
        0 <= y <= 10,
{
    while unknown() != 0
        invariant
            (x == 20) as int != 0 ==> (y != 0) as int != 0,
            0 <= y,
            0 <= x,
    {
        if x > i32::MAX - 10 || y > i32::MAX - 10 {
            break ;
        }
        x = x + 10;
        y = y + 10;
    }
    if x == 20 {
        assert(y != 0);
    }
}


fn valid_test_harness_foo(){
    foo(0, 5);
    foo(5, 0);
    foo(3, 7);
    foo(10, 5);
    foo(5, 10);
    foo(0, 0);
    foo(10, 10);
}

fn invalid_test_harness_foo(){
    foo(-1, 5);
    foo(5, 11);
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

// fn foo(mut x: i32, mut y: i32)
// {
//     while unknown() != 0
//     {
//         assert!((!(x == 20) ||  (y != 0)) && 0 <= y && 0 <= x);
//         if x > i32::MAX - 10 || y > i32::MAX - 10 {
//             break ;
//         }
//         x = x + 10;
//         y = y + 10;
//     }
//     assert!(!(x == 20) || (y != 0) && 0 <= y && 0 <= x);
//     if x == 20 {
//         assert!(y != 0);
//     }
// }

// fn valid_test_harness_foo(){
//     foo(0, 5);
//     foo(5, 0);
//     foo(3, 7);
//     foo(10, 5);
//     foo(5, 10);
//     foo(0, 0);
//     foo(10, 10);
// }

// fn main(){
//     valid_test_harness_foo();
// }