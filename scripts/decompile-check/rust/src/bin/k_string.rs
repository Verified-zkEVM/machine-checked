#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let s = String::from_utf8_lossy(&i.a).into_owned();
    outs(s.to_uppercase().as_bytes());
    out(s.chars().filter(|c| c.is_alphanumeric()).count() as u64);
    let t: String = i.b.iter().map(|&b| (b'a' + b % 26) as char).collect();
    outs(t.as_bytes());
    let parts: Vec<&str> = t.split('e').collect();
    out(parts.len() as u64);
    outs(parts.join("-").replace("a", "AA").as_bytes());
    out(t.find("ab").map(|x| x as u64).unwrap_or(999));
    let mut r = t.clone(); r.push_str(&s); r.truncate(r.len() / 2 & !3); outs(r.as_bytes());
    out(t.bytes().rev().position(|b| b == b'z').unwrap_or(77) as u64);
}
