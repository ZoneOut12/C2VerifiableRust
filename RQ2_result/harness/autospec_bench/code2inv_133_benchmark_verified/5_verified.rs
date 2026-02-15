fn main() {
    let mut x: i32 = 0;
    let mut size: i32 = 0;
    let mut y: i32 = 0;
    let mut z: i32 = 0;

    while x < size
    {
        let old_measure = size - x;
        assert!( (z >= y || x == 0) &&  0 <= x);
        x += 1;
        if z <= y {
            y = z;
        }
        assert!( (size - x) < old_measure );
    }
    assert!( (z >= y || x == 0) &&  0 <= x);

    if size > 0 {
        assert!(z >= y);
    }
}