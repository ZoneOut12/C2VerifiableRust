#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn is_power(x: int, n: int, r: int) -> bool;

#[verifier::external_body]
pub broadcast proof fn is_power_inductive()
    ensures
        forall|x: int| (is_power(x as int, 0 as int, 1 as int)),
        forall|x: int, n: int, r: int|
            (n > 0) as int != 0 ==> (((is_power(x as int, n - 1 as int, r as int))) as int != 0
                ==> ((is_power(x as int, n as int, r * x as int))) as int != 0) as int != 0,
{
}

#[verifier::external_body]
pub broadcast proof fn power_even()
    ensures
        forall|x: int, n: int, r: int|
            (n >= 0) as int != 0 ==> (((is_power(x * x as int, n as int, r as int))) as int != 0
                ==> ((is_power(x as int, n * 2 as int, r as int))) as int != 0) as int != 0,
{
}

#[verifier::external_body]
pub broadcast proof fn power_odd()
    ensures
        forall|x: int, n: int, rp: int|
            (n >= 0) as int != 0 ==> (((is_power(x * x as int, n as int, rp as int))) as int != 0
                ==> ((is_power(x as int, 2 * n + 1 as int, x * rp as int))) as int != 0) as int
                != 0,
{
}

#[verifier::external_body]
pub broadcast proof fn monotonic()
    ensures
        forall|x: int, n1: int, n2: int, r1: int, r2: int|
            (0 <= n1 <= n2) as int != 0 ==> (((is_power(x as int, n1 as int, r1 as int)) && (
            is_power(x as int, n2 as int, r2 as int))) as int != 0 ==> (r1 <= r2) as int
                != 0) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn power(x: i32, n: i32) -> (result: i32)
    requires
        0 <= n < i32::MAX,
        exists|m: int| (is_power(x as int, n as int, m as int)) && i32::MIN <= m <= i32::MAX,
    ensures
        (is_power(x as int, n as int, result as int)),
{
    broadcast use is_power_inductive, power_even, power_odd, monotonic;

    let mut r: i32 = 1;
    let mut i: i32 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            (is_power(x as int, i - 1 as int, r as int)),
        decreases n - i,
    {
        r *= x;
        i += 1;
    }
    r
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fast_power(x: u32, n: u32) -> (result: u32)
    ensures
        (is_power(x as int, n as int, result as int)),
{
    broadcast use is_power_inductive, power_even, power_odd, monotonic;

    let n_pre: u32 = n;
    let mut r: u32 = 1;
    let mut p: u32 = x;
    let mut n: u32 = n;
    while n > 0
        invariant
            0 <= n,
            forall|v: int|
                ((is_power(p as int, n as int, v as int))) as int != 0 ==> ((is_power(
                    x as int,
                    n_pre as int,
                    r * v as int,
                ))) as int != 0,
        decreases n,
    {
        if n % 2 == 1 {
            assert((is_power(p as int, n as int, r as int)));
            r = r * p;
        }
        p *= p;
        n /= 2;
    }
    assert((is_power(p as int, n as int, 1 as int)));
    r
}

fn main() {
}

} // verus!
