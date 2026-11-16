#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    println!("a line on stdout");
    eprintln!("a line on stderr: {}", i.u8());
    print!("{:?}", &i.a[..i.a.len().min(8)]);
    sp1_zkvm::io::write(1, &i.b[..i.b.len().min(20)]);
    out(i.u64());
    eprintln!("{:x}", i.u64());
}
