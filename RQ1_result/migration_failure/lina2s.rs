#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

struct vector<'a> {
    n: i32,
    v: &'a mut [i32],
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn predicate(v: i32) -> (result: bool)
    ensures
        result == 0 || result == 1,
{
    v % 2 == 0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn index_where<'a>(a: &mut vector<'a>, o: &mut vector<'a>)
    requires
        true,
        true,
        (old(a).v + (((0) as int)..((old(a).n - 1) as int)))@.len() >= 1,
        (old(o).v + (((0) as int)..((old(a).n - 1) as int)))@.len() >= 1,
        forall|i: i32|
            forall|j: i32|
                (0 <= i < old(a).n && 0 <= j < old(a).n) as int != 0 ==> (true) as int != 0,
        old(a).n > 0,
    ensures
        0 <= o.n <= a.n,
        forall|i: i32| (0 <= i < o.n) as int != 0 ==> (0 <= o.v@[(i) as int] < a.n) as int != 0,
        forall|i: i32|
            (0 < i < o.n) as int != 0 ==> (o.v@[(i - 1) as int] < o.v@[(i) as int]) as int != 0,
{
    let n: i32 = a.n;
    o.n = 0;

    let mut i: i32 = 0;
    while i < n
        invariant
            n == a.n,
            0 <= i <= n,
            0 <= o.n <= i,
            forall|j: i32| (0 <= j < o.n) as int != 0 ==> (0 <= o.v@[(j) as int] < i) as int != 0,
            forall|j: i32|
                (0 < j < o.n) as int != 0 ==> (o.v@[(j - 1) as int] < o.v@[(j) as int]) as int != 0,
        decreases n - i,
    {
        if predicate(a.v[i as usize]) {
            o.v[o.n as usize] = i;
            o.n += 1;
        }
        i += 1;
    }
}

fn main() {
}

} // verus!
