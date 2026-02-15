// RAC
fn unknown() -> i32 {
    kani::any()
}

fn assist(k: i32) -> bool{k != 40} //2A

#[kani::proof]
fn main() {
    let mut c: i32 = 0;
    while unknown() != 0
    {
        let k: i32 = kani::any();
        assert!(
            c <= 40 &&
            (!(c != 40) || (c <= 40)) &&
            (!(i32::MIN <= k && k <= i32::MAX) ||
                0 <= k && k <= c && assist(k) ) &&
            0 <= c &&
            (!(c != 40)) || ((c < 40))
        );
        assert!(assist(0)); //2a
        if unknown() != 0 {
            if c != 40 {
                c = c + 1;
            }
        } else {
            if c == 40 {
                c = 1;
            }
        }
    }
    let k: i32 = kani::any();
    assert!(
            c <= 40 &&
            (!(c != 40) || (c <= 40)) &&
            (!(i32::MIN <= k && k <= i32::MAX) ||
                0 <= k && k <= c && assist(k) ) &&
            0 <= c &&
            (!(c != 40)) || ((c < 40))
        );
    if c != 40 {
        assert!(c <= 40);
    }
}
