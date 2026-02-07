struct vector<'a> {
    n: i32,
    v: &'a mut [i32],
}

fn predicate(v: i32) -> bool {
    v % 2 == 0
}

fn index_where<'a>(a: &mut vector<'a>, o: &mut vector<'a>) {
    let n: i32 = a.n;
    o.n = 0;
    
    let mut i: i32 = 0;
    while i < n {
        if predicate(a.v[i as usize]) {
            o.v[o.n as usize] = i;
            o.n += 1;
        }
        i += 1;
    }
}