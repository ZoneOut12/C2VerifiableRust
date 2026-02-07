fn picker_first(x0: i32) -> i32 {
    0
}

fn pick_first_element(x6: &[i32], x7: i32) -> i32 {
    let x9: i32 = picker_first(x7);
    let x10: i32 = x6[x9 as usize];
    x10
}

fn pick_first_directly(x15: &[i32], x16: i32) -> i32 {
    let x18: i32 = x15[0];
    x18
}

fn picker_last(x23: i32) -> i32 {
    let x25: i32 = x23 - 1;
    x25
}

fn pick_last_element(x30: &[i32], x31: i32) -> i32 {
    let x33: i32 = picker_last(x31);
    let x34: i32 = x30[x33 as usize];
    x34
}

fn pick_last_directly(x39: &[i32], x40: i32) -> i32 {
    let x42: i32 = x40 - 1;
    let x43: i32 = x39[x42 as usize];
    x43
}