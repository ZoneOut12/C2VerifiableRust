#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn arr_sorted(arr: &[i32], begin: int, end: int) -> bool {
    forall|i: int, j: int|
        (begin <= i <= j < end) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0
}

pub open spec fn sorted(arr: &[i32], end: int) -> bool {
    (arr_sorted(arr, 0 as int, end as int))
}

pub open spec fn is_in_array(value: i32, arr: &[i32], begin: int, end: int) -> bool {
    exists|j: int| begin <= j < end && arr@[(j) as int] == value
}

pub open spec fn in_array(value: i32, arr: &[i32], end: int) -> bool {
    (is_in_array(value as i32, arr, 0 as int, end as int))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bsearch(arr: &[i32], len: usize, value: i32) -> (result: usize)
    requires
        arr@.len() >= len - 1 + 1,
        (sorted(arr, len as int)),
    ensures
        ((in_array(value as i32, arr, len as int))) ==> (0 <= result < len) && (arr@[(
        result) as int] == value),
        ((!(((in_array(value as i32, arr, len as int))) as int != 0))) ==> (result == len),
{
    if len == 0 {
        return len;
    }
    let mut low: usize = 0;
    let mut up: usize = len;
    while low < up
        invariant
            0 <= low && up <= len,
            forall|i: int|
                (0 <= i < len && arr@[(i) as int] == value) as int != 0 ==> (low <= i < up) as int
                    != 0,
        decreases up - low,
    {
        let mid: usize = low + (up - low) / 2;
        if arr[mid] > value {
            up = mid;
        } else if arr[mid] < value {
            low = mid + 1;
        } else {
            return mid;
        }
    }
    len
}

fn main() {
}

} // verus!
