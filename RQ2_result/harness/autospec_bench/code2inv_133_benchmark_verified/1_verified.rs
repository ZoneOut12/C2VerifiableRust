fn main() {
    let mut x: i64 = 1;
    let mut y: i64 = 0;

    while y < 100000
    {
        let old_measure = 100000 - y;
        assert!( 
            y <= x && y <= 100000 && x == ((y - 1) * y) / 2 + 1 && 1 <= x && 0 <= y
        );
        x = x + y;
        y = y + 1;
        assert!( (100000 - y) < old_measure );
    }
    assert!( 
            y <= x && y <= 100000 && x == ((y - 1) * y) / 2 + 1 && 1 <= x && 0 <= y
        );
    assert!((x >= y));
}