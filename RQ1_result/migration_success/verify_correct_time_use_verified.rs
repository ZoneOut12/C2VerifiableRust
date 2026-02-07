#[allow(unused_imports)]
use vstd::math::*;
use vstd::prelude::*;
use vstd::slice::*;
verus! {

use tag_class::*;
use asn1_type::*;

#[derive(PartialEq)]
enum tag_class {
    CLASS_UNIVERSAL = 0x00,
    CLASS_APPLICATION = 0x01,
    CLASS_CONTEXT_SPECIFIC = 0x02,
    CLASS_PRIVATE = 0x03,
}

#[derive(PartialEq)]
enum asn1_type {
    ASN1_TYPE_BOOLEAN = 0x01,
    ASN1_TYPE_INTEGER = 0x02,
    ASN1_TYPE_BIT_STRING = 0x03,
    ASN1_TYPE_OCTET_STRING = 0x04,
    ASN1_TYPE_NULL = 0x05,
    ASN1_TYPE_OID = 0x06,
    ASN1_TYPE_ENUMERATED = 0x0a,
    ASN1_TYPE_SEQUENCE = 0x10,
    ASN1_TYPE_SET = 0x11,
    ASN1_TYPE_PrintableString = 0x13,
    ASN1_TYPE_T61String = 0x14,
    ASN1_TYPE_IA5String = 0x16,
    ASN1_TYPE_UTCTime = 0x17,
    ASN1_TYPE_GeneralizedTime = 0x18,
}

const X509_FILE_NUM: i32 = 3;

const X509_FILE_LINE_NUM_ERR: i32 = X509_FILE_NUM * 100000 + 0;

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn verify_correct_time_use(time_type: asn1_type, yyyy: u16) -> (result: i32)
    ensures
        result < 0 || result == 0,
        (result == -1) as int != 0 ==> ((time_type != ASN1_TYPE_UTCTime && time_type
            != ASN1_TYPE_GeneralizedTime)) as int != 0,
        ((time_type != ASN1_TYPE_UTCTime && time_type != ASN1_TYPE_GeneralizedTime)) as int != 0
            ==> (result == -1) as int != 0,
{
    let mut ret: i32 = 0;
    match time_type {
        ASN1_TYPE_UTCTime => {
            if yyyy <= 2049 {
                ret = 0;
            } else {
                ret = -X509_FILE_LINE_NUM_ERR;
            }
        },
        ASN1_TYPE_GeneralizedTime => {
            if yyyy >= 2050 {
                ret = 0;
            } else {
                ret = -X509_FILE_LINE_NUM_ERR;
            }
        },
        _ => {
            ret = -1;
        },
    }
    ret
}

#[verifier::loop_isolation(false)]
#[verifier::exec_allows_no_decreases_clause]
fn main() {
    let mut time_type: asn1_type = ASN1_TYPE_IA5String;
    let yyyy: u16 = 0;
    let mut result: i32 = verify_correct_time_use(time_type, yyyy);
    assert(result == -1);
    time_type = ASN1_TYPE_UTCTime;
    result = verify_correct_time_use(time_type, yyyy);
    assert(result < 0 || result == 0);
}

} // verus!
