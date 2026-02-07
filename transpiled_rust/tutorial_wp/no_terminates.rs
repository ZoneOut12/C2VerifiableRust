static mut counter: u32 = 0;

fn does_not_terminate() {
    while true {
        unsafe {
            counter += 1;
        }
    }
}