#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

const X509_FILE_NUM: i32 = 1;

const X509_FILE_LINE_NUM_ERR: i32 = X509_FILE_NUM * 100000;

#[verifier::external_body]
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
    let mut ret: i32 = 0;//0
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
            ret = -X509_FILE_LINE_NUM_ERR;//0
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

fn CheckPost_check_ia5_string(buf: &[u8], len: u32, result: i32)
    requires
        result < 0 || result == 0,
        ((len == 0)) as int != 0 ==> (result < 0) as int != 0,
        (result == 0) as int != 0 ==> (forall|i: int|
            (0 <= i < len) as int != 0 ==> ((buf@[(i) as int] <= 0x7f)) as int != 0) as int != 0,
        (result == -X509_FILE_LINE_NUM_ERR) as int != 0 ==> (exists|i: int|
            0 <= i < len && buf@[(i) as int] > 0x7f) as int != 0,
        exists|i: int|
            (0 <= i < len && buf@[(i) as int] > 0x7f) as int != 0 ==> (result
                == -X509_FILE_LINE_NUM_ERR) as int != 0,
{}

fn valid_test_harness(){
    let buf: [u8; 5] = [0x41, 0x42, 0x43, 0x44, 0x45];
    let len: u32 = 5;
    check_ia5_string(&buf, len);
    let result: i32 = 0;
    CheckPost_check_ia5_string(&buf, len, result);

    let buf = vec![0x7F, 0x7F, 0x7F];
    let len: u32 = 3;
    check_ia5_string(&buf, len);
    let result: i32 = 0;
    CheckPost_check_ia5_string(&buf, len, result);

    let buf = vec![0x00, 0x20, 0x7E];
    let len: u32 = 3;
    check_ia5_string(&buf, len);
    let result: i32 = 0;
    CheckPost_check_ia5_string(&buf, len, result);

    let buf = vec![0x61, 0x30, 0x20];
    let len: u32 = 3;
    check_ia5_string(&buf, len);
    let result: i32 = 0;
    CheckPost_check_ia5_string(&buf, len, result);

    let buf = vec![0x0A];
    let len: u32 = 1;
    check_ia5_string(&buf, len);
    let result: i32 = 0;
    CheckPost_check_ia5_string(&buf, len, result);

    let buf = vec![0x7F];
    let len: u32 = 1;
    check_ia5_string(&buf, len);
    let result: i32 = 0;
    CheckPost_check_ia5_string(&buf, len, result);

    let buf = vec![0x80u8];
    let len: u32 = 1;
    check_ia5_string(&buf, len);
    let result: i32 = -100000;
    CheckPost_check_ia5_string(&buf, len, result);
}

fn invalid_test_harness(){
    let buf = vec![0x41];
    let len: u32 = 0;
    check_ia5_string(&buf, len);

    let len: u32 = 5;
    check_ia5_string(None, len);
}

} // verus!

// RAC
// const X509_FILE_NUM: i32 = 1;

// const X509_FILE_LINE_NUM_ERR: i32 = X509_FILE_NUM * 100000;

// fn check_ia5_string(buf: &[u8], len: u32) -> i32 {
//     let mut ret: i32 = 0; //0
//     if len == 0 {
//         return -X509_FILE_LINE_NUM_ERR;
//     }
//     let mut i: u32 = 0;
//     while i < len
//     {
//         let old_measure = len - i;
//         let x: u32 = kani::any();
//         assert!(
//             (!(u32::MIN <= x && x <= u32::MAX) || (!(0 <= x && x < i) || (buf[x as usize] <= 0x7f))) &&
//             (!(ret == 0) || (!(u32::MIN <= x && x <= u32::MAX) || (!(0 <= x && x < i) || (buf[x as usize] <= 0x7f))))
//         );
//         if buf[i as usize] > 0x7f {
//             ret = -X509_FILE_LINE_NUM_ERR; //0
//             return -X509_FILE_LINE_NUM_ERR;
//         }
//         i += 1;
//         assert!((len - i) < old_measure);
//     }
//     let x: u32 = kani::any();
//     assert!(
//         (!(u32::MIN <= x && x <= u32::MAX) || (!(0 <= x && x < i) || (buf[x as usize] <= 0x7f))) &&
//         (!(ret == 0) || (!(u32::MIN <= x && x <= u32::MAX) || (!(0 <= x && x < i) || (buf[x as usize] <= 0x7f))))
//     );
//     0
// }

// #[kani::proof]
// fn main() {
//     let buf: [u8; 5] = [0; 5];
//     let len: u32 = 5;

//     let ret: i32 = check_ia5_string(&buf, len);
//     let i: u32 = kani::any();
//     assert!(
//         (!(ret == -X509_FILE_LINE_NUM_ERR)
//             || !(!(u32::MIN <= i && i <= u32::MAX)
//                 || !(0 <= i && i < len && buf[(i) as usize] > 0x7f))) &&
//         (!(ret == 0)
//             || (!(u32::MIN <= i && i <= u32::MAX)
//                 || (!(0 <= i && i < len) || (buf[(i) as usize] <= 0x7f))))
//     );
// }

// #[kani::proof]
// fn valid_test_harness() {
//     let buf: [u8; 5] = [0x41, 0x42, 0x43, 0x44, 0x45];
//     let len: u32 = 5;
//     check_ia5_string(&buf, len);

//     let buf = vec![0x7F, 0x7F, 0x7F];
//     let len: u32 = 3;
//     check_ia5_string(&buf, len);

//     let buf = vec![0x00, 0x20, 0x7E];
//     let len: u32 = 3;
//     check_ia5_string(&buf, len);

//     let buf = vec![0x61, 0x30, 0x20];
//     let len: u32 = 3;
//     check_ia5_string(&buf, len);

//     let buf = vec![0x0A];
//     let len: u32 = 1;
//     check_ia5_string(&buf, len);

//     let buf = vec![0x7F];
//     let len: u32 = 1;
//     check_ia5_string(&buf, len);

//     let buf = vec![0x80u8];
//     let len: u32 = 1;
//     check_ia5_string(&buf, len);
// }
