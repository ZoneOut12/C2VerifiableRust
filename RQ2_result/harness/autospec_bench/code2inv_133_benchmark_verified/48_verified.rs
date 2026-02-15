#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

spec fn assist(k: int) -> bool{ 0 <= k } //2A

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32)
    requires
        n > 0,
{
    let mut c: i32 = 0;

    while unknown() != 0
        invariant
            (c == n) as int != 0 ==> (forall|k: int|
                (#[trigger] assist(k) && k < c) as int != 0 ==> (k != n) as int != 0) as int != 0, //2B
            c != n || c <= n,
            0 <= c,
            ((c == n)) as int != 0 ==> ((n > -1)) as int != 0,
    {
        if unknown() != 0 {
            if c != n {
                if c >= 2147483647 {
                    break ;
                }
                c += 1;
            }
        } else {
            if c == n {
                c = 1;
            }
        }
    }
    if c == n {
        assert(n > -1);
    }
}

fn valid_test_harness_foo(){
    foo(5);
    foo(10);
    foo(42);
    foo(100);
    foo(1000);
    foo(1);
    foo(2147483647);
}

fn invalid_test_harness_foo(){
    foo(0);
    foo(-5);
}

fn main() {
}

} // verus!

// RAC
// fn unknown() -> i32 {
//     kani::any()
// }

// fn assist(k: i32) -> bool{ 0 <= k } //2A

// fn foo(n: i32)
// {
//     let mut c: i32 = 0;

//     while unknown() != 0
//     {
//         let k: i32 = kani::any();
//         assert!(
//             (!(c == n) || (!(i32::MIN <= k && k <= i32::MAX) ||
//                 (!(assist(k) && k < c) || (k != n) ))) && //2B
//             (c != n || c <= n) &&
//             0 <= c &&
//             (!(c == n) || (n > -1))
//         );
//         if unknown() != 0 {
//             if c != n {
//                 if c >= 2147483647 {
//                     break ;
//                 }
//                 c += 1;
//             }
//         } else {
//             if c == n {
//                 c = 1;
//             }
//         }
//     }
//     let k: i32 = kani::any();
//     assert!(
//             (!(c == n) || (!(i32::MIN <= k && k <= i32::MAX) ||
//                 (!(assist(k) && k < c) || (k != n) ))) && //2B
//             (c != n || c <= n) &&
//             0 <= c &&
//             (!(c == n) || (n > -1))
//         );
//     if c == n {
//         assert!(n > -1);
//     }
// }

// #[kani::proof]
// fn valid_test_harness_foo(){
//     foo(5);
//     foo(10);
//     foo(42);
//     foo(100);
//     foo(1000);
//     foo(1);
//     foo(2147483647);
// }

// fn main(){}