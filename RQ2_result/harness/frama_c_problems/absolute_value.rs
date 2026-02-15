verus! {

pub mod libmath {
    #[allow(unused_imports)]


    use vstd::math::*;
    use vstd::prelude::*;
    #[allow(unused_imports)]
    use vstd::slice::*;

    #[verifier::external_fn_specification]
    pub fn i32_abs(x: i32) -> (result: i32)
        ensures
            result >= 0,
            result == if x < 0 {
                -x as int
            } else {
                x as int
            },
    {
        x.abs()
    }

}

} // verus!
#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
#[allow(unused_imports)]
use vstd::slice::*;

verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn my_abs(val: i32) -> (result: i32)
    requires
        val > i32::MIN,
    ensures
        result >= 0,
        ((val >= 0) as int != 0 ==> (result == val) as int != 0) && ((val < 0) as int != 0 ==> (
        result == -val) as int != 0),
{
    val.abs()
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: i32)
    requires
        a > i32::MIN,
{
    let b: i32 = my_abs(-42);
    let c: i32 = my_abs(42);
    let d: i32 = my_abs(a);
}

fn CheckPre_my_abs(val: i32)
    requires
        val > i32::MIN,
{}

fn CheckPost_my_abs(val: i32, result: i32)
    requires
        result >= 0,
        ((val >= 0) as int != 0 ==> (result == val) as int != 0) && ((val < 0) as int != 0 ==> (
        result == -val) as int != 0),
{}

fn CheckPre_foo(a: i32)
    requires
        a > i32::MIN,
{}

fn main() {
}

fn valid_test_harness_abs() {
    // Test case 1: Valid - zero
    let val1 = 0;
    CheckPre_my_abs(val1);
    let result1 = 0;
    CheckPost_my_abs(val1, result1);

    // Test case 2: Valid - positive number
    let val2 = 42;
    CheckPre_my_abs(val2);
    let result2 = 42;
    CheckPost_my_abs(val2, result2);

    // Test case 3: Valid - negative number
    let val3 = -42;
    CheckPre_my_abs(val3);
    let result3 = 42;
    CheckPost_my_abs(val3, result3);

    // Test case 4: Valid - positive large number
    let val4 = 1000;
    CheckPre_my_abs(val4);
    let result4 = 1000;
    CheckPost_my_abs(val4, result4);

    // Test case 5: Valid - negative large number
    let val5 = -1000;
    CheckPre_my_abs(val5);
    let result5 = 1000;
    CheckPost_my_abs(val5, result5);

    // Test case 8: Boundary - minimal valid negative input
    let val8 = -2147483647; // i32::MIN + 1
    CheckPre_my_abs(val8);
    let result8 = 2147483647;
    CheckPost_my_abs(val8, result8);

    // Test case 9: Boundary - zero
    let val9 = 0;
    CheckPre_my_abs(val9);
    let result9 = 0;
    CheckPost_my_abs(val9, result9);
}

fn invalid_test_harness_abs() {
    // Test case 6: Invalid - INT_MIN (Violation: requires val > INT_MIN)
    let val6 = i32::MIN;
    CheckPre_my_abs(val6);

    // Test case 7: Invalid - explicit INT_MIN value
    let val7 = -2147483648;
    CheckPre_my_abs(val7);
}

fn valid_test_harness_foo() {
    // Test case 1: Typical positive input
    let a1 = 10;
    CheckPre_foo(a1);

    // Test case 2: Minimal valid negative input
    let a2 = -2147483647; // i32::MIN + 1
    CheckPre_foo(a2);

    // Test case 3: Zero input
    let a3 = 0;
    CheckPre_foo(a3);
}

fn invalid_test_harness_foo() {
    // Test case 4: Invalid - INT_MIN
    let a4 = i32::MIN;
    CheckPre_foo(a4);
}

} // verus!
