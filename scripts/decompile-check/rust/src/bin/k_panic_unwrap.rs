#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let (a, b) = (i.u32(), i.u8());
    out(a as u64);
    let q = a.checked_div(b as u32 & 0x70).unwrap_or(1);
    out(q as u64);
    let r = (a as u8).checked_add(b).expect("the sum of two bytes fits a byte");
    out(r as u64);
    if r > 200 { panic!("too large: {}", r); }
    let v: Vec<u8> = Vec::new();
    out(*v.get(b as usize).or(Some(&r)).unwrap() as u64);
    let o: Option<u8> = if b & 1 == 1 { None } else { Some(b) };
    out(o.unwrap() as u64);
}
