#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn is_fibo(n: int, r: int) -> bool;

#[verifier::external_body]
pub broadcast proof fn is_fibo_inductive()
    ensures
        (is_fibo(0 as int, 1 as int)),
        (is_fibo(1 as int, 1 as int)),
        forall|n: int, p_1: int, p_2: int|
            (n > 1) as int != 0 ==> (((is_fibo(n - 2 as int, p_2 as int))) as int != 0 ==> (((
            is_fibo(n - 1 as int, p_1 as int))) as int != 0 ==> ((is_fibo(
                n as int,
                p_2 + p_1 as int,
            ))) as int != 0) as int != 0) as int != 0,
{
}

#[verifier::external_body]
pub broadcast proof fn fib_monotonic()
    ensures
        forall|i: int, j: int, n1: int, n2: int|
            (i <= j && (is_fibo(i as int, n1 as int)) && (is_fibo(j as int, n2 as int))) as int != 0
                ==> (n1 <= n2) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn helper(n: i32, p_1: i32, p_2: i32)
    requires
        n > 1 && (is_fibo(n - 2 as int, p_2 as int)) && (is_fibo(n - 1 as int, p_1 as int)),
    ensures
        (is_fibo(n as int, p_2 + p_1 as int)),
{
    broadcast use is_fibo_inductive, fib_monotonic;

}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn fibo(n: i32) -> (result: i32)
    requires
        n >= 0,
        exists|m: int| (is_fibo(n as int, m as int)) && 0 < m <= i32::MAX,
    ensures
        (is_fibo(n as int, result as int)),
{
    broadcast use is_fibo_inductive, fib_monotonic;

    if n < 2 {
        return 1;
    }
    let mut p_1: i32 = 1;
    let mut r: i32 = p_1 + 1;

    helper(2, p_1, 1);
    assert((is_fibo(2 as int, r as int)));

    let mut i: i32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            (is_fibo(i - 1 as int, p_1 as int)),
            (is_fibo(i as int, r as int)),
        decreases n - i,
    {
        let x: i32 = r + p_1;
        helper(i + 1, r, p_1);
        p_1 = r;
        r = x;
        i += 1;
    }
    r
}

fn main() {
}

} // verus!
