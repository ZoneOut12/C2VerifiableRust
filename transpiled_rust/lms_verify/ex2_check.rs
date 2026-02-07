fn pick_index(x0: i32) -> i32 {
    0
}

fn pick_element(x6: &[i32], x7: i32) -> i32 {
    let x9: i32 = pick_index(x7);
    let x10: i32 = x6[x9 as usize];
    x10
}

fn pick_first(x15: &[i32]) -> i32 {
    let x17: i32 = x15[0];
    x17
}