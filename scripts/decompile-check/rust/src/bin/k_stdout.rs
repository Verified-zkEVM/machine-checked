#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    println!("a line on stdout");
    eprintln!("a line on stderr: {}", i.u8());
    print!("{:?}", &i.a[..i.a.len().min(8)]);
    write(1, &i.b[..i.b.len().min(20)]);
    out(i.u64());
    eprintln!("{:x}", i.u64());
}
