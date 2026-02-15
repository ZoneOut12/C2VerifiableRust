#[kani::proof]
fn main() {
    let mut A: [i32; 2048] = [0;2048];
    let mut i: i32 = 0;
    while i < 1024
    {
        let old_measuere = 1024 - i;
        let j: i32 = kani::any();
        assert!(
            (!(i32::MIN <= j && j < i32::MAX) || (!(0 <= j && j < i) || A[j as usize] == j)) &&
            0 <= i && i <= 1024
        );
        A[i as usize] = i;
        i += 1;
        assert!(1024 - i < old_measuere);
    }
    let j: i32 = kani::any();
    assert!(
        (!(i32::MIN <= j && j < i32::MAX) || (!(0 <= j && j < i) || A[j as usize] == j)) &&
        0 <= i && i <= 1024
    );
    assert!(A[1023] == 1023);
}