fn array_swap(arr: &mut [i32], n: i32, n1: i32, n2: i32) {
    let temp = arr[n1 as usize];
    arr[n1 as usize] = arr[n2 as usize];
    arr[n2 as usize] = temp;
}