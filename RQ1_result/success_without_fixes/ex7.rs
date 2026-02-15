#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn member(p: &[i32], n: i32, v: i32) -> (result: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
    ensures
        (result == -1) as int != 0 ==> (!(((exists|i: i32|
            0 <= i < n && p@[(i) as int] == v)) as int != 0)) as int != 0,
        (result != -1) as int != 0 ==> (0 <= result < n && p@[(result) as int] == v) as int != 0,
{
    let mut i: i32 = 0;
    while i < n
        invariant
            (0 <= i <= n),
            !(((exists|j: i32| 0 <= j < i && p@[(j) as int] == v)) as int != 0),
        decreases n - i,
    {
        if p[i as usize] == v {
            return i;
        }
        i += 1;
    }
    -1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn member_noreturn(p: &[i32], n: i32, v: i32) -> (result: i32)
    requires
        n > 0 && p@.len() >= n - 1 + 1,
    ensures
        (result == -1) as int != 0 ==> (!(((exists|i: i32|
            0 <= i < n && p@[(i) as int] == v)) as int != 0)) as int != 0,
        (result != -1) as int != 0 ==> (0 <= result < n && p@[(result) as int] == v) as int != 0,
{
    let mut r: i32 = -1;
    let mut i: i32 = 0;
    while i < n
        invariant
            (0 <= i <= n),
            (r == -1) as int != 0 ==> (!(((exists|j: i32| 0 <= j < i && p@[(j) as int] == v)) as int
                != 0)) as int != 0,
            (r != -1) as int != 0 ==> (0 <= r < n && p@[(r) as int] == v) as int != 0,
        decreases n - i,
    {
        if r == -1 && p[i as usize] == v {
            r = i;
        }
        i += 1;
    }
    r
}

fn main() {
}

} // verus!
