#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bsearch(arr: &[i32], len: usize, value: i32) -> (result: usize)
    requires
        arr@.len() >= len - 1 + 1,
        forall|i: int, j: int|
            (0 <= i <= j < len) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0,
    ensures
        (exists|j: int| 0 <= j < len && arr@[(j) as int] == value) ==> (0 <= result < len) && (
        arr@[(result) as int] == value),
        (forall|j: int| (0 <= j < len) as int != 0 ==> (arr@[(j) as int] != value) as int != 0)
            ==> (result == len),
{
    if len == 0 {
        return 0;
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
