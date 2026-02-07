fn search(array: &mut [i32], length: usize, element: i32) -> Option<&mut i32> {
    let mut i: usize = 0;
    while i < length {
        if array[i] == element {
            return Some(&mut array[i]);
        }
        i += 1;
    }
    None
}

fn foo(array: &mut [i32], length: usize) {
    let p: Option<&mut i32> = search(array, length, 0);
    if let Some(p_ref) = p {
        *p_ref += 1;
    }
}