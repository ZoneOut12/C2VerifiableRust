fn array_find(arr: &[i32], n: i32, x: i32) -> i32 {
    let mut i: i32 = 0;
    while i < n {
        if arr[i as usize] == x {
            return i;
        }
        i += 1;
    }
    -1
}