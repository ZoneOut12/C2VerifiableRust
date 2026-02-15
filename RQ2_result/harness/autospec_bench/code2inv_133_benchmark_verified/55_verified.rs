#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::external_body]
fn unknown() -> (result: i32) {
    unimplemented!();
}

spec fn assist(i: int) -> bool{ 1 <= i } //2a

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32)
    requires
        n > 0,
{
    let mut c: i32 = 0;
    while unknown() != 0
        invariant
            n != c,
            c >= 0 && c <= n,
            (c > n) as int != 0 ==> (c == n) as int != 0,
            (c > n) as int != 0 ==> (c == n + 1) as int != 0,
            c <= n,
            forall|k: int|
                (#[trigger] assist(k) && k <= c) as int != 0 ==> ((exists|i: int| #[trigger] assist(i) && i <= n && i == c)) as int != 0,//2b
            0 <= c,
    {
        if unknown() != 0 {
            if c > n {
                c += 1;
            }
        } else {
            if c == n {
                c = 1;
            }
        }
    }
    if c < 0 {
        if c > n {
            assert(c == n);
        }
    }
}

fn valid_test_harness_foo(){
    foo(3);
    foo(4);
    foo(5);
    foo(10);
    foo(7);
    foo(1);
    foo(2);
}

fn invalid_test_harness_foo(){
    foo(0);
    foo(-1);
}

fn main() {
}

} // verus!

// RAC
// fn unknown() -> i32 {
//     kani::any()
// }

// fn assist(i: i32) -> bool{ 1 <= i } //2a

// fn foo(n: i32)
// {
//     let mut c: i32 = 0;
//     while unknown() != 0
//     {
//         let k:i32 = kani::any();
//         let i:i32 = kani::any();
//         assert!(    
//             n != c &&
//             (c >= 0 && c <= n) &&
//             (!(c > n) || (c == n)) &&
//             (!(c > n) || (c == n + 1)) &&
//             c <= n &&
//             (!(i32::MIN <= k && k <= i32::MAX) || (!(assist(k) && k <= c) || !(!(i32::MIN <= i && i <= i32::MAX) || !(assist(i) && i <= n && i == c)))) && //2b
//             0 <= c,
//         );
//         if unknown() != 0 {
//             if c > n {
//                 c += 1;
//             }
//         } else {
//             if c == n {
//                 c = 1;
//             }
//         }
//     }
//     let k:i32 = kani::any();
//     let i:i32 = kani::any();
//     assert!(    
//         n != c &&
//         (c >= 0 && c <= n) &&
//         (!(c > n) || (c == n)) &&
//         (!(c > n) || (c == n + 1)) &&
//         c <= n &&
//         (!(i32::MIN <= k && k <= i32::MAX) || (!(assist(k) && k <= c) || !(!(i32::MIN <= i && i <= i32::MAX) || !(assist(i) && i <= n && i == c)))) && //2b
//         0 <= c,
//     );
//     if c < 0 {
//         if c > n {
//             assert!(c == n);
//         }
//     }
// }

// #[kani::proof]
// fn valid_test_harness_foo(){
//     foo(3);
//     foo(4);
//     foo(5);
//     foo(10);
//     foo(7);
//     foo(1);
//     foo(2);
// }
