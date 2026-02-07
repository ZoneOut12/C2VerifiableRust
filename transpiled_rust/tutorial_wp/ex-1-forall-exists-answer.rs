fn pred(value: i32) -> i32 {
    if 0 <= value && value <= 42 {
        1
    } else {
        0
    }
}

fn forall_pred(array: &[i32], len: usize) -> i32 {
    let mut i: usize = 0;
    while i < len {
        if pred(array[i]) == 0 {
            return 0;
        }
        i += 1;
    }
    1
}

fn exists_pred(array: &[i32], len: usize) -> i32 {
    let mut i: usize = 0;
    while i < len {
        if pred(array[i]) != 0 {
            return 1;
        }
        i += 1;
    }
    0
}

fn none_pred(array: &[i32], len: usize) -> i32 {
    (exists_pred(array, len) == 0) as i32
}

fn some_not_pred(array: &[i32], len: usize) -> i32 {
    (forall_pred(array, len) == 0) as i32
}