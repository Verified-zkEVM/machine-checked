#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    enum E { Num(i64), Add(Box<E>, Box<E>), Mul(Box<E>, Box<E>), Neg(Box<E>), If(Box<E>, Box<E>, Box<E>), Var(u8) }
    fn build(i: &mut In, d: u32) -> E {
        let b = i.u8();
        if d == 0 { return if b & 1 == 0 { E::Num(b as i64 - 100) } else { E::Var(b >> 1) }; }
        match b % 6 {
            0 => E::Num(i.u16() as i16 as i64), 1 => E::Add(Box::new(build(i, d - 1)), Box::new(build(i, d - 1))),
            2 => E::Mul(Box::new(build(i, d - 1)), Box::new(build(i, d - 1))), 3 => E::Neg(Box::new(build(i, d - 1))),
            4 => E::If(Box::new(build(i, d - 1)), Box::new(build(i, d - 1)), Box::new(build(i, d - 1))), _ => E::Var(b),
        }
    }
    fn eval(e: &E, env: &[i64; 4]) -> i64 {
        match e {
            E::Num(n) => *n, E::Add(a, b) => eval(a, env).wrapping_add(eval(b, env)), E::Mul(a, b) => eval(a, env).wrapping_mul(eval(b, env)),
            E::Neg(a) => eval(a, env).wrapping_neg(), E::If(c, a, b) => if eval(c, env) > 0 { eval(a, env) } else { eval(b, env) },
            E::Var(v) => env[*v as usize & 3],
        }
    }
    fn size(e: &E) -> u64 { match e { E::Add(a, b) | E::Mul(a, b) => 1 + size(a) + size(b), E::Neg(a) => 1 + size(a), E::If(a, b, c) => 1 + size(a) + size(b) + size(c), _ => 1 } }
    for _ in 0..3 { let e = build(&mut i, 4); out(size(&e)); out(eval(&e, &[3, -7, 100, 0]) as u64); out(eval(&e, &[-1, 2, -3, 4]) as u64); }
}
