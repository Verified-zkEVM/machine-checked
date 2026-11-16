//! What every guest of the check shares: its input and its output.
//!
//! A guest reads the two hint vectors of a test input and shows what it computes by
//! committing it, so that a wrong value anywhere on the way is a different run.

/// The bytes of the input, read in turn; past the end they are zeros.
pub struct In {
    pub a: Vec<u8>,
    pub b: Vec<u8>,
    pos: usize,
}

impl In {
    pub fn new() -> In {
        In { a: sp1_zkvm::io::read_vec(), b: sp1_zkvm::io::read_vec(), pos: 0 }
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
    sp1_zkvm::io::commit_slice(&x.to_le_bytes());
}

/// Show a wide value.
pub fn out128(x: u128) {
    sp1_zkvm::io::commit_slice(&x.to_le_bytes());
}

/// Show bytes.
pub fn outs(x: &[u8]) {
    sp1_zkvm::io::commit_slice(x);
}
