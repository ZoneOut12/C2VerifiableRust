fn unknown1() -> i32 { unimplemented!(); }
fn unknown2() -> i32 { unimplemented!(); }
fn unknown3() -> i32 { unimplemented!(); }
fn unknown4() -> i32 { unimplemented!(); }

fn main() {
    let mut w: i32 = 1;
    let mut z: i32 = 0;
    let mut x: i32 = 0;
    let mut y: i32 = 0;

    while unknown1() != 0 {
        while unknown2() != 0 {
            if w % 2 == 1 {
                if x == 2147483647 { break; }
                x += 1;
            }
            if z % 2 == 0 {
                if y == 2147483647 { break; }
                y += 1;
            }
        }
        if x <= (2147483647 - 1) / 2 {
            z = x + y;
            w = z + 1;
        }
    }

    // verus_assert(1);
}