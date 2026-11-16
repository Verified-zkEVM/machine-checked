#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut o = Vec::new();
    for c in i.a.chunks(3) {
        let n = (c[0] as u32) << 16 | (*c.get(1).unwrap_or(&0) as u32) << 8 | *c.get(2).unwrap_or(&0) as u32;
        o.push(T[(n >> 18) as usize & 63]); o.push(T[(n >> 12) as usize & 63]);
        o.push(if c.len() > 1 { T[(n >> 6) as usize & 63] } else { b'=' });
        o.push(if c.len() > 2 { T[n as usize & 63] } else { b'=' });
    }
    outs(&o);
    let mut d = Vec::new(); let mut acc = 0u32; let mut bits = 0;
    for &ch in &o { if let Some(p) = T.iter().position(|&t| t == ch) { acc = acc << 6 | p as u32; bits += 6; if bits >= 8 { bits -= 8; d.push((acc >> bits) as u8); } } }
    out((d == i.a) as u64); out(d.len() as u64);
}
