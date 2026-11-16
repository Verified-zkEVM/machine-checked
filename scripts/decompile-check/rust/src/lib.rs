//! What every guest of the check shares: its input, its output, and the machine under it.
//!
//! A guest reads the two hint vectors of a test input and shows what it computes by
//! committing it, so that a wrong value anywhere on the way is a different run.
//!
//! The same source is three programs:
//!
//! * an **SP1 guest** (RISC-V), on `sp1-zkvm`, with Rust's standard library;
//! * a **bare program for AArch64** and one **for x86-64**, without an operating system and
//!   without the standard library (`bare`): its own entry, stack, heap and panic, and four
//!   system calls, made by `svc #0` or `syscall`, with the numbers SP1 gives them.
//!
//! A guest starts with `guests::entry!(main);` and `use guests::*;`, which on the bare
//! machines also brings in what the standard prelude would (`Vec`, `String`, `format!`, …)
//! and a module `std` with the parts of the standard library that `alloc` and `core` have.

#![cfg_attr(not(target_os = "zkvm"), no_std)]

#[cfg(not(target_os = "zkvm"))]
extern crate alloc;

#[cfg(not(target_os = "zkvm"))]
mod bare;
#[cfg(not(target_os = "zkvm"))]
pub use bare::*;

/// The guest's `main`.
#[cfg(target_os = "zkvm")]
#[macro_export]
macro_rules! entry {
    ($main:path) => {
        sp1_zkvm::entrypoint!($main);
    };
}

/// The next hint vector.
#[cfg(target_os = "zkvm")]
pub fn read_vec() -> Vec<u8> {
    sp1_zkvm::io::read_vec()
}

/// Write bytes to a file: 1 is the standard output, 2 the standard error.
#[cfg(target_os = "zkvm")]
pub fn write(fd: u32, buf: &[u8]) {
    sp1_zkvm::io::write(fd, buf)
}

/// Show bytes: they are part of what the run is.
#[cfg(target_os = "zkvm")]
pub fn outs(x: &[u8]) {
    sp1_zkvm::io::commit_slice(x);
}

/// The bytes of the input, read in turn; past the end they are zeros.
pub struct In {
    pub a: Vec<u8>,
    pub b: Vec<u8>,
    pos: usize,
}

impl In {
    pub fn new() -> In {
        In { a: read_vec(), b: read_vec(), pos: 0 }
    }
    pub fn u8(&mut self) -> u8 {
        let v = self.a.get(self.pos).copied().unwrap_or(0);
        self.pos += 1;
        v
    }
    pub fn u16(&mut self) -> u16 {
        self.u8() as u16 | (self.u8() as u16) << 8
    }
    pub fn u32(&mut self) -> u32 {
        self.u16() as u32 | (self.u16() as u32) << 16
    }
    pub fn u64(&mut self) -> u64 {
        self.u32() as u64 | (self.u32() as u64) << 32
    }
    pub fn u128(&mut self) -> u128 {
        self.u64() as u128 | (self.u64() as u128) << 64
    }
}

/// Show a value.
pub fn out(x: u64) {
    outs(&x.to_le_bytes());
}

/// Show a wide value.
pub fn out128(x: u128) {
    outs(&x.to_le_bytes());
}
