fn my_atoi(a: &String) -> i32 {
    let m: i32 = (i32::MAX / 10) - 10;
    let mut r: i32 = 0;
    let mut index: usize = 0;
    let bytes = a.as_bytes();
    
    while index < bytes.len() && bytes[index] >= b'0' && bytes[index] <= b'9' {
        if r > m {
            return -1;
        }
        r = 10 * r + (bytes[index] as i32 - b'0' as i32);
        index += 1;
    }
    r
}