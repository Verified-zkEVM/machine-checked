#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    trait Shape { fn area(&self) -> u64; }
    struct Sq(u32); struct Rect(u32, u32);
    impl Shape for Sq { fn area(&self) -> u64 { self.0 as u64 * self.0 as u64 } }
    impl Shape for Rect { fn area(&self) -> u64 { self.0 as u64 * self.1 as u64 } }
    fn total<S: Shape>(xs: &[S]) -> u64 { xs.iter().map(|s| s.area()).sum() }
    fn apply(f: &mut dyn FnMut(u64) -> u64, n: u64) -> u64 { (0..n).map(|k| f(k)).fold(0, |a, b| a ^ b) }
    fn twice<F: Fn(u64) -> u64>(f: F, x: u64) -> u64 { f(f(x)) }
    let sq: Vec<Sq> = (0..6).map(|_| Sq(i.u16() as u32)).collect();
    let re: Vec<Rect> = (0..6).map(|_| Rect(i.u16() as u32, i.u8() as u32)).collect();
    out(total(&sq)); out(total(&re));
    let mut count = 0u64; let k = i.u64();
    out(apply(&mut |x| { count += x; x.wrapping_mul(k) ^ count }, 20)); out(count);
    out(twice(|x| x.wrapping_mul(k).rotate_left(5), 3)); out(twice(|x| x + 1, k));
    let fs: Vec<Box<dyn Fn(u64) -> u64>> = vec![Box::new(move |x| x ^ k), Box::new(|x| x >> 3), Box::new(move |x| x.wrapping_add(k))];
    out(fs.iter().fold(i.u64(), |x, f| f(x)));
}
