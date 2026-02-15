#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(n: i32, m: i32, l: i32) -> (result: i32)
    requires
        i32::MIN < 3 * n < i32::MAX,
        i32::MIN < m && m < i32::MAX,
        i32::MIN < l && l < i32::MAX,
        i32::MIN < m + l < i32::MAX,
{
    if 3 * n <= m + l {
        let mut i: i32 = 0;
        while i < n
            invariant
                0 <= i,
            decreases n - i,
        {
            let mut j: i32 = 2 * i;
            while j < 3 * i
                invariant
                    i <= n,
                    2 * i <= j,
                    0 <= i,
                decreases 3 * i - j,
            {
                let mut k: i32 = i;
                while k < j
                    decreases j - k,
                {
                    assert(k - i <= 2 * n);
                    k += 1;
                }
                j += 1;
            }
            i += 1;
        }
    }
    0
}

fn valid_test_harness(){
    let mut result: i32 = foo(1, 1, 1);
    result = foo(2, 3, 4);
    result = foo(10, 20, 10);
    result = foo(715827882, 0, 0);
    result = foo(-10, -5, -5);
    result = foo(715827882, 1, 0);
    result = foo(1, -2147483647, 1);
}

fn invalid_test_harness(){
    foo(715827883, 0, 0);
    foo(1, 2147483646, 2);
}

fn main() {
}

} // verus!

// RAC
// fn foo(n: i32, m: i32, l: i32) -> i32
// {
//     if 3 * n <= m + l {
//         let mut i: i32 = 0;
//         while i < n
//         {
//             let old_measure = n - i;
//             assert!(0 <= i);
//             let mut j: i32 = 2 * i;
//             while j < 3 * i
//             {
//                 let old_measure_2 = 3 * i - j;
//                 assert!(
//                     i <= n &&
//                     2 * i <= j &&
//                     0 <= i
//                 );
//                 let mut k: i32 = i;
//                 while k < j
//                 {
//                     let old_measure_3 = j - k;
//                     assert!(k - i <= 2 * n);
//                     k += 1;
//                     assert!(old_measure_3 > j - k);
//                 }
//                 j += 1;
//                 assert!(old_measure_2 > 3 * i - j);
//             }
//             assert!(
//                 i <= n &&
//                 2 * i <= j &&
//                 0 <= i
//             );
//             i += 1;
//             assert!(n - i < old_measure);
//         }
//         assert!(0 <= i);
//     }
//     0
// }

// fn valid_test_harness(){
//     let mut result: i32 = foo(1, 1, 1);
//     result = foo(2, 3, 4);
//     result = foo(10, 20, 10);
//     result = foo(715827882, 0, 0);
//     result = foo(-10, -5, -5);
//     result = foo(715827882, 1, 0);
//     result = foo(1, -2147483647, 1);
// }

// fn main(){
//     valid_test_harness();
// }