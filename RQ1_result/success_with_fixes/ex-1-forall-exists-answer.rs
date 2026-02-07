#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn pred(value: i32) -> (result: i32)
    ensures
        (result) as int != 0 <==> ((0 <= value <= 42)) as int != 0,
{
    if 0 <= value && value <= 42 {
        1
    } else {
        0
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn forall_pred(array: &[i32], len: usize) -> (result: i32)
    requires
        array@.len() >= len - 1 + 1,
    ensures
        (result) as int != 0 <==> ((forall|i: int|
            (0 <= i < len) as int != 0 ==> (0 <= #[trigger] array@[(i) as int] <= 42) as int != 0)) as int//2B
            != 0,
{
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|j: int| (0 <= j < i) as int != 0 ==> (0 <= #[trigger] array@[(j) as int] <= 42) as int != 0,//2B
        decreases len - i,
    {
        if pred(array[i]) == 0 {
            return 0;
        }
        i += 1;
    }
    1
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn exists_pred(array: &[i32], len: usize) -> (result: i32)
    requires
        array@.len() >= len - 1 + 1,
    ensures
        (result) as int != 0 <==> ((exists|i: int|
            0 <= i < len && 0 <= #[trigger] array@[(i) as int] <= 42)) as int != 0,//2B
{
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            forall|j: int|
                (0 <= j < i) as int != 0 ==> ((!(((0 <= #[trigger] array@[(j) as int] <= 42)) as int //2B
                    != 0))) as int != 0,
        decreases len - i,
    {
        if pred(array[i]) != 0 {
            return 1;
        }
        i += 1;
    }
    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn none_pred(array: &[i32], len: usize) -> (result: i32)
    requires
        array@.len() >= len - 1 + 1,
    ensures
        (result) as int != 0 <==> ((forall|i: int|
            (0 <= i < len) as int != 0 ==> ((!(((0 <= #[trigger] array@[(i) as int] <= 42)) as int//2B
                != 0))) as int != 0)) as int != 0,
{
    (exists_pred(array, len) == 0) as i32
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn some_not_pred(array: &[i32], len: usize) -> (result: i32)
    requires
        array@.len() >= len - 1 + 1,
    ensures
        (result) as int != 0 <==> ((exists|i: int|
            0 <= i < len && (!(((0 <= #[trigger] array@[(i) as int] <= 42)) as int != 0)))) as int != 0,//2B
{
    (forall_pred(array, len) == 0) as i32
}

fn main() {
}

} // verus!
