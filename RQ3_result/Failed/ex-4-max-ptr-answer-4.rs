#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

exec static mut h: i32 = 0;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn max_ptr(a: Option<&i32>, b: Option<&i32>) -> (result: i32)
    requires
        (a).is_none() || true,
        (b).is_none() || true,
    ensures
        result == i32::MIN || result == ((a).unwrap()@) || result == ((b).unwrap()@),
        ((a).is_none() && (b).is_none()) ==> (result == i32::MIN),
        ((a).is_none() && (b).is_some()) ==> (result == ((b).unwrap()@)),
        ((a).is_some() && (b).is_none()) ==> (result == ((a).unwrap()@)),
        ((a).is_some() && (b).is_some() && ((a).unwrap()@) >= ((b).unwrap()@)) ==> (result == ((
        a).unwrap()@)),
        ((a).is_some() && (b).is_some() && ((a).unwrap()@) < ((b).unwrap()@)) ==> (result == ((
        b).unwrap()@)),
{
    if a.is_none() && b.is_none() {
        return i32::MIN;
    }
    if a.is_none() {
        return *b.unwrap();
    }
    if b.is_none() {
        return *a.unwrap();
    }
    let a_val = a.unwrap();
    let b_val = b.unwrap();
    if *a_val < *b_val {
        *b_val
    } else {
        *a_val
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    unsafe {
        h = 42;
    }
    let a: i32 = 24;
    let b: i32 = 42;
    let x: i32 = max_ptr(Some(&a), Some(&b));
    assert(x == 42);
    assert(h == 42);
}

} // verus!
