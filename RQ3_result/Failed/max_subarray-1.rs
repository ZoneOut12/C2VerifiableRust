#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub uninterp spec fn sum(array: &[i32], begin: int, end: int) -> int;

#[verifier::external_body]
pub broadcast proof fn empty()
    ensures
        forall|a: &[i32], b: int, e: int|
            (b >= e) as int != 0 ==> ((sum(a, b as int, e as int)) == 0) as int != 0,
{
}

#[verifier::external_body]
pub broadcast proof fn range()
    ensures
        forall|a: &[i32], b: int, e: int|
            (b < e) as int != 0 ==> ((sum(a, b as int, e as int)) == (sum(
                a,
                b as int,
                e - 1 as int,
            )) + a@[(e - 1) as int]) as int != 0,
{
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_subarray(a: &[i32], len: usize) -> (result: i32)
    requires
        a@.len() >= len - 1 + 1,
        forall|i: int, j: int| i32::MIN <= (sum(a, i as int, j as int)) <= i32::MAX,
    ensures
        forall|l: int, h: int|
            (0 <= l <= h <= len) as int != 0 ==> ((sum(a, l as int, h as int)) <= result) as int
                != 0,
        exists|l: int, h: int| 0 <= l <= h <= len && (sum(a, l as int, h as int)) == result,
{
    broadcast use empty, range;

    let mut max: i32 = 0;
    let mut cur: i32 = 0;
    let mut cur_low: usize = 0;
    let mut low: usize = 0;
    let mut high: usize = 0;

    let mut i: usize = 0;
    while i < len
        invariant
            low <= high <= i <= len && cur_low <= i,
            cur == (sum(a, cur_low as int, i as int)) <= max == (sum(a, low as int, high as int)),
            forall|l: int|
                (0 <= l <= i) as int != 0 ==> ((sum(a, l as int, i as int)) <= cur) as int != 0,
            forall|l: int, h: int|
                (0 <= l <= h <= i) as int != 0 ==> ((sum(a, l as int, h as int)) <= max) as int
                    != 0,
        decreases len - i,
    {
        assert((cur + a@[(i) as int] == (sum(a, cur_low as int, i + 1 as int))));
        cur += a[i];
        if cur < 0 {
            cur = 0;
            cur_low = i + 1;
        }
        if cur > max {
            max = cur;
            low = cur_low;
            high = i + 1;
        }
        i += 1;
    }
    max
}

fn main() {
}

} // verus!
