#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn alphabet_letter(c: char) -> (result: i32)
    ensures
        (result) as int != 0 <==> (('a' <= c <= 'z') || ('A' <= c <= 'Z')) as int != 0,
{
    if ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') {
        1
    } else {
        0
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut r: i32;
    r = alphabet_letter('x');
    assert(r != 0);//1
    r = alphabet_letter('H');
    assert(r != 0);//1
    r = alphabet_letter(' ');
    assert((!((r) as int != 0)));
}

} // verus!
