fn bsearch(arr: &[i32], len: i32, value: i32) -> i32 {
    if len == 0 {
        return -1;
    }
    let mut low: i32 = 0;
    let mut up: i32 = len - 1;
    while low <= up {
        let mid: i32 = low + (up - low) / 2;
        if arr[mid as usize] > value {
            up = mid - 1;
        } else if arr[mid as usize] < value {
            low = mid + 1;
        } else {
            return mid;
        }
    }
    -1
}