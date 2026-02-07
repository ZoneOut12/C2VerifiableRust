#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn bsearch(arr: &[i32], len: i32, value: i32) -> (result: i32)
    requires
        arr@.len() >= len - 1 + 1,
        forall|i: int, j: int|
            (0 <= i <= j < len) as int != 0 ==> (arr@[(i) as int] <= arr@[(j) as int]) as int != 0,
        len >= 0,
    ensures
        -1 <= result < len,
        (exists|j: int| 0 <= j < len && arr@[(j) as int] == value) ==> (arr@[(result) as int]
            == value),
        (forall|j: int| (0 <= j < len) as int != 0 ==> (arr@[(j) as int] != value) as int != 0)
            ==> (result == -1),
{
    if len == 0 {
        return -1;
    }
    let mut low: i32 = 0;
    let mut up: i32 = len - 1;
    while low <= up
        invariant
            0 <= low && up < len,
            forall|i: int|
                (0 <= i < len && arr@[(i) as int] == value) as int != 0 ==> (low <= i <= up) as int
                    != 0,
        decreases up - low,
    {
        let mid: i32 = low + (up - low) / 2;
        if arr[mid as usize] > value {
            up = mid - 1;
        } else if arr[mid as usize] < value {
            low = mid + 1;
        } else {
            return mid;
        }
    }
    -1
}

fn main() {
}

} // verus!
