#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn sum_of_n_integers(n: int) -> int 
    decreases n //2E
{
    if (n <= 0) {
        0
    } else {
        (sum_of_n_integers(n - 1 as int)) + n
    }
}

pub open spec fn sum_of_range_of_integers(fst: int, lst: int) -> int 
    decreases lst - fst + u128::MAX //2E
{
    (if (lst <= fst) {
        lst
    } else {
        lst + (sum_of_range_of_integers(fst as int, lst - 1 as int))
    })
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn lemma_value_of_sum_of_n_integers_2(n: u32)
    ensures
        (n * (n + 1)) / 2 == (sum_of_n_integers(n as int)),
{
    let mut i: u32 = 0;
    while i < n
        invariant
            0 <= i <= n,
            (i * (i + 1)) == 2 * (sum_of_n_integers(i as int)),
        decreases n - i,
    {
        i += 1;
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn lemma_value_of_sum_of_range_of_integers(fst: i32, lst: i32)
    requires
        fst <= lst,
    ensures
        ((lst - fst + 1) * (fst + lst)) / 2 == (sum_of_range_of_integers(fst as int, lst as int)),
{
    let mut i: i32 = fst;
    while i < lst
        invariant
            fst <= i <= lst,
            (i - fst + 1) * (fst + i) == 2 * (sum_of_range_of_integers(fst as int, i as int)),
        decreases lst - i,
    {
        i += 1;
        assert((i - fst + 1) * (fst + i) == 2 * (sum_of_range_of_integers(fst as int, i as int))) by (nonlinear_arith) requires (i - 1 - fst + 1) * (fst + i - 1) == 2 * (sum_of_range_of_integers(fst as int, (i-1) as int)) && sum_of_range_of_integers(fst as int,i as int) == sum_of_range_of_integers(fst as int ,(i-1) as int)+i;//2A
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn sum_n(n: u32) -> (result: u32)
    requires
        n * (n + 1) <= u32::MAX,
    ensures
        result == (sum_of_n_integers(n as int)),
{
    lemma_value_of_sum_of_n_integers_2(n);
    assert(n * (n + 1) >= 0);
    (n * (n + 1)) / 2
}

fn main() {
}

} // verus!
