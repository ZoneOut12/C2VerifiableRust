fn matcher(x0: &String) -> i32 {
    let x2: i32 = x0.len() as i32;
    let x3: i32 = (0 < x2) as i32;
    let x6: i32;
    if x3 != 0 {
        let x4: u8 = x0.as_bytes()[0];
        let x5: i32 = (x4 == b'a') as i32;
        x6 = x5;
    } else {
        x6 = 0;
    }
    let x7: i32;
    if x6 != 0 {
        x7 = 1;
    } else {
        x7 = 0;
    }
    x7
}