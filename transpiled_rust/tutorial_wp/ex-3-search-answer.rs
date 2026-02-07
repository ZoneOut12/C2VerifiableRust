fn search(array: &[i32], length: u32, element: i32) -> u32 {
    if length == 0 {
        return u32::MAX;
    }
    if array[(length - 1) as usize] == element {
        return length - 1;
    } else {
        return search(array, length - 1, element);
    }
}