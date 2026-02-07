#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn even_natural(n: int) -> bool;

#[verifier::external_body]
pub broadcast proof fn even_natural_inductive()
    ensures
        (even_natural(0 as int)),
        forall|n: int|
            (#[trigger](even_natural(n as int))) as int != 0 ==> ((even_natural(n + 2 as int))) as int != 0, //2B
        (!(((even_natural(1 as int))) as int != 0)),
        forall|n: int|
            ((!((#[trigger](even_natural(n as int))) as int != 0))) as int != 0 ==> ((!(((even_natural( //2B
                n + 2 as int,
            ))) as int != 0))) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn foo() {
    broadcast use even_natural_inductive;

    assert((even_natural(4 as int)));
    assert((even_natural(42 as int)));
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bar() {
    broadcast use even_natural_inductive;

    let a: i32 = 1;
    assert((!(((even_natural(a as int))) as int != 0)));
}

fn main() {
}

} // verus!
