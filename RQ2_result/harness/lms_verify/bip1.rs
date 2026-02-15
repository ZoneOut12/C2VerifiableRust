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

fn CheckPost_d1(c: char, result: i32)
    requires
        -1 <= result <= 9,
        (d(c as int)) == result,
{}

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

fn CheckPost_e1(i: i32, result: char)
    requires
        '0' <= result <= '9' || result == ' ',
        (e(i as int)) == result,
{}

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

fn CheckPost_ed(c: char, result: char)
    requires
        ('0' <= c <= '9') as int != 0 ==> (result == c) as int != 0,
        (c != result) as int != 0 ==> (result == ' ') as int != 0,
        (e((d(c as int)) as int)) == result,
{}

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

fn CheckPost_de(i: i32, result: i32)
    requires
        (0 <= i <= 9) as int != 0 ==> (result == i) as int != 0,
        (i != result) as int != 0 ==> (result == -1) as int != 0,
        (d((e(i as int)) as int)) == result,
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn ded(c: char) -> (result: i32)
    ensures
        (d((e((d(c as int)) as int)) as int)) == (d(c as int)),
{
    d1(e1(d1(c)))
}

fn CheckPost_ded(c: char, result: i32)
    requires
        (d((e((d(c as int)) as int)) as int)) == (d(c as int)),
{}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn ede(i: i32) -> (result: char)
    ensures
        (e((d((e(i as int)) as int)) as int)) == (e(i as int)),
{
    e1(d1(e1(i)))
}

fn CheckPost_ede(i: i32, result: char)
    requires
        (e((d((e(i as int)) as int)) as int)) == (e(i as int)),
{}

fn main() {
}

fn test_case_1() {
    let c: char = '0';
    let i: i32  = 0;

    d1(c);
    let r_d1: i32 = 0;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = '0';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = '0';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = 0;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = 0;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = '0';
    CheckPost_ede(i, r_ede);
}

fn test_case_2() {
    let c: char = '5';
    let i: i32  = 5;

    d1(c);
    let r_d1: i32 = 5;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = '5';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = '5';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = 5;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = 5;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = '5';
    CheckPost_ede(i, r_ede);
}

fn test_case_3() {
    let c: char = '9';
    let i: i32  = 9;

    d1(c);
    let r_d1: i32 = 9;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = '9';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = '9';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = 9;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = 9;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = '9';
    CheckPost_ede(i, r_ede);
}

fn test_case_4() {
    let c: char = 'A';
    let i: i32  = 10;

    d1(c);
    let r_d1: i32 = -1;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = ' ';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = ' ';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = -1;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = -1;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = ' ';
    CheckPost_ede(i, r_ede);
}

fn test_case_5() {
    let c: char = ' ';
    let i: i32  = -1;

    d1(c);
    let r_d1: i32 = -1;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = ' ';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = ' ';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = -1;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = -1;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = ' ';
    CheckPost_ede(i, r_ede);
}

fn test_case_6() {
    let c: char = '/';
    let i: i32  = -2;

    d1(c);
    let r_d1: i32 = -1;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = ' ';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = ' ';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = -1;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = -1;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = ' ';
    CheckPost_ede(i, r_ede);
}

fn test_case_7() {
    let c: char = ':';
    let i: i32  = 42;

    d1(c);
    let r_d1: i32 = -1;
    CheckPost_d1(c, r_d1);

    e1(i);
    let r_e1: char = ' ';
    CheckPost_e1(i, r_e1);

    ed(c);
    let r_ed: char = ' ';
    CheckPost_ed(c, r_ed);

    de(i);
    let r_de: i32  = -1;
    CheckPost_de(i, r_de);

    ded(c);
    let r_ded: i32 = -1;
    CheckPost_ded(c, r_ded);

    ede(i);
    let r_ede: char = ' ';
    CheckPost_ede(i, r_ede);
}


} // verus!
