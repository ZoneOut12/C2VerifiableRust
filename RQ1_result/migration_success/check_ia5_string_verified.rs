#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

const X509_FILE_NUM: i32 = 1;

const X509_FILE_LINE_NUM_ERR: i32 = X509_FILE_NUM * 100000;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn check_ia5_string(buf: &[u8], len: u32) -> (result: i32)
    requires
        len > 0,
        buf@.len() >= (len - 1) + 1,
    ensures
        result < 0 || result == 0,
        ((len == 0)) as int != 0 ==> (result < 0) as int != 0,
        (result == 0) as int != 0 ==> (forall|i: int|
            (0 <= i < len) as int != 0 ==> ((buf@[(i) as int] <= 0x7f)) as int != 0) as int != 0,
        (result == -X509_FILE_LINE_NUM_ERR) as int != 0 ==> (exists|i: int|
            0 <= i < len && buf@[(i) as int] > 0x7f) as int != 0,
        exists|i: int|
            (0 <= i < len && buf@[(i) as int] > 0x7f) as int != 0 ==> (result
                == -X509_FILE_LINE_NUM_ERR) as int != 0,
{
    if len == 0 {
        return -X509_FILE_LINE_NUM_ERR;
    }
    let mut i: u32 = 0;
    while i < len
        invariant
            forall|x: int| (0 <= x < i) as int != 0 ==> ((buf@[(x) as int] <= 0x7f)) as int != 0,
            (ret == 0) as int != 0 ==> (forall|x: int|
                (0 <= x < i) as int != 0 ==> ((buf@[(x) as int] <= 0x7f)) as int != 0) as int != 0,
        decreases (len - i),
    {
        if buf[i as usize] > 0x7f {
            return -X509_FILE_LINE_NUM_ERR;
        }
        i += 1;
    }

    0
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let buf: [u8; 5] = [0;5];
    let len: u32 = 5;

    let ret: i32 = check_ia5_string(&buf, len);
    assert((ret == -X509_FILE_LINE_NUM_ERR) as int != 0 ==> (exists|i: int|
        0 <= i < len && buf@[(i) as int] > 0x7f) as int != 0);
    assert((ret == 0) as int != 0 ==> (forall|i: int|
        (0 <= i < len) as int != 0 ==> ((buf@[(i) as int] <= 0x7f)) as int != 0) as int != 0);
}

} // verus!
