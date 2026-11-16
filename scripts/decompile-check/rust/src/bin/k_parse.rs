#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    fn num(i: &mut In) -> String { let n = i.u8() % 12; (0..n).map(|_| { let b = i.u8(); (if b % 9 == 8 { b'x' } else { b'0' + b % 10 }) as char }).collect() }
    fn both(a: &str, b: &str) -> Result<i64, std::num::ParseIntError> { Ok(a.parse::<i64>()? - b.parse::<u32>()? as i64) }
    for _ in 0..8 {
        let (a, b) = (num(&mut i), num(&mut i));
        match both(&a, &b) { Ok(v) => out(v as u64), Err(e) => outs(format!("{e}").as_bytes()) }
        out(a.parse::<u8>().map(|x| x as u64).unwrap_or(1000)); out(i64::from_str_radix(&b, 7).unwrap_or(-1) as u64);
    }
    out("3.25".parse::<f64>().unwrap().to_bits()); out(format!("{}", i.u8()).parse::<u16>().unwrap() as u64);
}
