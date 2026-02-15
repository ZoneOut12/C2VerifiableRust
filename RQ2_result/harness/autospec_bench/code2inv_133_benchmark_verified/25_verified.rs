#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(mut x: i32)
    requires
        (x == 10000),
{
    while x > 0
        invariant
            x <= 10000,
            0 <= x,
        decreases x,
    {
        x = x - 1;
    }
    assert((x == 0));
}

fn valid_test_harness_foo(){
    foo(10000);
}

fn invalid_test_harness_foo(){
    foo(9999);
    foo(10001);
}

fn main() {
}

} // verus!

// RAC
// fn foo(mut x: i32)
// {
//     while x > 0
//     {
//         let old_measure = x;
//         assert!(
//             x <= 10000 &&
//             0 <= x
//         );
//         x = x - 1;
//         assert!(x < old_measure);
//     }
//     assert!(
//             x <= 10000 &&
//             0 <= x
//         );
//     assert!((x == 0));
// }

// fn valid_test_harness_foo(){
//     foo(10000);
// }

// fn main(){
//     valid_test_harness_foo();
// }