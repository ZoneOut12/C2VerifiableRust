#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn ax_b(a: int, x: int, b: int) -> int {
    a * x + b
}

pub proof fn ax_b_monotonic_neg()
    ensures
        forall|a: int, b: int, i: int, j: int|
            (a < 0) as int != 0 ==> ((i <= j) as int != 0 ==> ((ax_b(a as int, i as int, b as int))
                >= (ax_b(a as int, j as int, b as int))) as int != 0) as int != 0,
{
}

pub proof fn ax_b_monotonic_pos()
    ensures
        forall|a: int, b: int, i: int, j: int|
            (a > 0) as int != 0 ==> ((i <= j) as int != 0 ==> ((ax_b(a as int, i as int, b as int))
                <= (ax_b(a as int, j as int, b as int))) as int != 0) as int != 0,
{
}

pub proof fn ax_b_monotonic_nul()
    ensures
        forall|a: int, b: int, i: int, j: int|
            (a == 0) as int != 0 ==> ((ax_b(a as int, i as int, b as int)) == (ax_b(
                a as int,
                j as int,
                b as int,
            ))) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn function(a: i32, x: i32) -> (result: i32)
    requires
        i32::MIN <= a * x <= i32::MAX,
        i32::MIN <= (ax_b(a as int, x as int, 4 as int)) <= i32::MAX,
    ensures
        result == (ax_b(a as int, x as int, 4 as int)),
{
    a * x + 4
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo(a: i32, x: i32, y: i32)
    requires
        i32::MIN <= a * x <= i32::MAX,
        i32::MIN <= a * y <= i32::MAX,
        a > 0,
        i32::MIN <= (ax_b(a as int, x as int, 4 as int)) <= i32::MAX,
        i32::MIN <= (ax_b(a as int, y as int, 4 as int)) <= i32::MAX,
{
    let mut fmin: i32;
    let mut fmax: i32;
    if x < y {
        fmin = function(a, x);
        fmax = function(a, y);
    } else {
        fmin = function(a, y);
        fmax = function(a, x);
    }
    assert(fmin <= fmax);
}

fn main() {
}

} // verus!
