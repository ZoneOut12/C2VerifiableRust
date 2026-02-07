#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

pub open spec fn d(c: int) -> int {
    if (0 <= c - '0' <= 9) {
        c - '0'
    } else {
        -1
    }
}

pub open spec fn e(i: int) -> int {
    if (0 <= i <= 9) {
        i + '0'
    } else {
        ' ' as int //1
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn d1(c: char) -> (result: i32)
    ensures
        -1 <= result <= 9,
        (d(c as int)) == result,
{
    if c >= '0' && c <= '9' {
        (c as u8 - '0' as u8) as i32
    } else {
        -1
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn e1(i: i32) -> (result: char)
    ensures
        '0' <= result <= '9' || result == ' ',
        (e(i as int)) == result,
{
    if 0 <= i && i <= 9 {
        (i as u8 + '0' as u8) as char
    } else {
        ' '
    }
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn ed(c: char) -> (result: char)
    ensures
        ('0' <= c <= '9') as int != 0 ==> (result == c) as int != 0,
        (c != result) as int != 0 ==> (result == ' ') as int != 0,
        (e((d(c as int)) as int)) == result,
{
    e1(d1(c))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn de(i: i32) -> (result: i32)
    ensures
        (0 <= i <= 9) as int != 0 ==> (result == i) as int != 0,
        (i != result) as int != 0 ==> (result == -1) as int != 0,
        (d((e(i as int)) as int)) == result,
{
    d1(e1(i))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn ded(c: char) -> (result: i32)
    ensures
        (d((e((d(c as int)) as int)) as int)) == (d(c as int)),
{
    d1(e1(d1(c)))
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn ede(i: i32) -> (result: char)
    ensures
        (e((d((e(i as int)) as int)) as int)) == (e(i as int)),
{
    e1(d1(e1(i)))
}

fn main() {
}

} // verus!
