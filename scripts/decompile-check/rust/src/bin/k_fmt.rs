#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let (x, y, z) = (i.u64(), i.u32() as i32, i.u8());
    let s = format!("{} {:x} {:?} {:08b} {:>12} {:+}", x, y, (z, x as i16), z, y, y);
    outs(s.as_bytes());
    let v: Vec<u16> = (0..5).map(|_| i.u16()).collect();
    outs(format!("{:?} {:#x?}", v, &v[..2]).as_bytes());
    outs(format!("{:.3} {:e}", x as f64 / 1000.0, y as f64).as_bytes());
    println!("stdout {} {}", x, z);
    outs(format!("{:?} {:?}", Some(z), if z > 100 { Ok(x) } else { Err("small") }).as_bytes());
}
