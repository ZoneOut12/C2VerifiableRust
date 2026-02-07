fn index_where_even(x0: &[i32], x1: i32, x2: &mut [i32]) -> i32 {
    let mut x5: i32 = 0;
    let mut x6: i32 = 0;
    while x6 < x1 {
        let x7: i32 = x0[x6 as usize];
        let x8: i32 = x7 % 2;
        let x9: bool = x8 == 0;
        if x9 {
            let x10: i32 = x5;
            x2[x10 as usize] = x6;
            x5 += 1;
        }
        x6 += 1;
    }
    let x62: i32 = x5;
    x62
}