#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn my_atoi(a: &String) -> (result: i32)
    requires
        (((a)@.len() - 1)) >= 0 && ((forall|i: int|
            0 <= i < a@.len() - 1 ==> (a@[(i) as int] != '\0')) && a@[a@.len() - 1] == '\0'),
    ensures
        0 <= result || result == -1,
{
    let m: i32 = (i32::MAX / 10) - 10;
    let mut r: i32 = 0;
    let mut index: usize = 0;
    let bytes = a.as_bytes();

    while index < bytes.len() && bytes[index] >= b'0' && bytes[index] <= b'9'
        invariant
            (((s)@.len() - 1)) >= 0 && s@.len() >= (((s)@.len() - 1)) + 1,
            0 <= r,
        decreases (((s)@.len() - 1)),
    {
        if r > m {
            return -1;
        }
        r = 10 * r + (bytes[index] as i32 - b'0' as i32);
        index += 1;
    }
    r
}

fn main() {
}

} // verus!
