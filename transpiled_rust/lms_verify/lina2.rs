fn predicate(v: i32) -> bool {
    v % 2 == 0
}

fn index_where(v: &[i32], n: i32, o: &mut [i32]) -> i32 {
    let mut r: i32 = 0;
    let mut i: i32 = 0;
    while i < n {
        if predicate(v[i as usize]) {
            o[r as usize] = i;
            r += 1;
        }
        i += 1;
    }
    r
}