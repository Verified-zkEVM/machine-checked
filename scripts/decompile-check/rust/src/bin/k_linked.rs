#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    use std::rc::Rc; use std::cell::RefCell;
    struct Node { v: u8, next: Option<Box<Node>> }
    let mut head: Option<Box<Node>> = None;
    for &b in i.a.iter().take(90) { head = Some(Box::new(Node { v: b, next: head })); }
    let mut rev: Option<Box<Node>> = None;
    while let Some(mut n) = head { head = n.next.take(); if n.v % 3 != 0 { n.next = rev; rev = Some(n); } }
    let mut h = 0u64; let mut p = &rev; let mut len = 0u64;
    while let Some(n) = p { h = h.wrapping_mul(131).wrapping_add(n.v as u64); len += 1; p = &n.next; }
    out(h); out(len);
    let shared = Rc::new(RefCell::new(Vec::<u16>::new()));
    let pushers: Vec<Rc<RefCell<Vec<u16>>>> = (0..4).map(|_| shared.clone()).collect();
    for (k, r) in pushers.iter().enumerate() { r.borrow_mut().push(i.u16() ^ k as u16); }
    out(Rc::strong_count(&shared) as u64); out(shared.borrow().iter().map(|&x| x as u64).sum());
}
