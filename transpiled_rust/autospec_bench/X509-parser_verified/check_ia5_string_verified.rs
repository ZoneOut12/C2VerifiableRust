const X509_FILE_NUM: i32 = 1;
const X509_FILE_LINE_NUM_ERR: i32 = X509_FILE_NUM * 100000;

fn check_ia5_string(buf: &[u8], len: u32) -> i32 {
    if len == 0 {
        return -X509_FILE_LINE_NUM_ERR;
    }

    let mut i: u32 = 0;
    while i < len {
        if buf[i as usize] > 0x7f {
            return -X509_FILE_LINE_NUM_ERR;
        }
        i += 1;
    }

    0
}

fn main() {
    let buf: [u8; 5] = [0; 5];
    let len: u32 = 5;

    let ret: i32 = check_ia5_string(&buf, len);
    // verus_assert(1);
    // verus_assert(2);
}