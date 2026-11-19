//! The first Rust examples: arithmetic, a branch and a loop over a slice.
#![no_std]

#[no_mangle]
pub extern "C" fn add3(a: u64, b: u64, c: u64) -> u64 {
    a.wrapping_add(b).wrapping_add(c)
}

#[no_mangle]
pub extern "C" fn max_u64(a: u64, b: u64) -> u64 {
    if a > b { a } else { b }
}

#[no_mangle]
pub extern "C" fn sum_slice(xs: &[u64]) -> u64 {
    let mut s: u64 = 0;
    for x in xs {
        s = s.wrapping_add(*x);
    }
    s
}

#[no_mangle]
pub extern "C" fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}
