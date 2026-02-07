static mut __BLAST_NONDET: i32 = 0;
static mut MAXPATHLEN: i32 = 0;

fn unknown() -> i32 {
    unimplemented!();
}

fn main() {
    if unsafe { MAXPATHLEN } > 0 {
    } else {
        return;
    }
    let mut buf_off: i32 = 0;
    let mut pattern_off: i32 = 0;
    let mut bound_off: i32 = 0 + (unsafe { MAXPATHLEN } + 1) - 1;
    let mut glob3_pathbuf_off: i32 = buf_off;
    let mut glob3_pathend_off: i32 = buf_off;
    let mut glob3_pathlim_off: i32 = bound_off;
    let mut glob3_pattern_off: i32 = pattern_off;
    let mut glob3_dc: i32 = 0;
    while true {
        if glob3_pathend_off + glob3_dc >= glob3_pathlim_off {
            break;
        } else {
            glob3_dc += 1;
            // verus_assert(1);
            // verus_assert(2);
            if unknown() != 0 {
                break;
            }
        }
    }
}