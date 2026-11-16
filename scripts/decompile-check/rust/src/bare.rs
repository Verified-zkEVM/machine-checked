//! The machine under a bare guest: no operating system, four system calls.
//!
//! A system call has a number and three arguments and gives one result. On AArch64 it is
//! `svc #0` with the number in `x8`, the arguments in `x0` to `x2` and the result in `x0`; on
//! x86-64 it is `syscall` with the number in `rax`, the arguments in `rdi`, `rsi` and `rdx`
//! and the result in `rax`. The calls are SP1's, by SP1's numbers: `HALT` (0, the exit code),
//! `WRITE` (2: a file, an address, a length), `HINT_LEN` (0xF0: the length of the next hint
//! vector) and `HINT_READ` (0xF1: an address and that length).

use core::alloc::{GlobalAlloc, Layout};
use core::arch::{asm, global_asm};
use core::fmt::Write;

pub use alloc::borrow::ToOwned;
pub use alloc::boxed::Box;
pub use alloc::string::{String, ToString};
pub use alloc::vec::Vec;
pub use alloc::{format, vec};

/// The parts of the standard library a guest names by `std::`.
pub mod std {
    pub use alloc::{collections, rc};
    pub use core::{cell, hash, num};
}

#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn syscall(n: u64, a: u64, b: u64, c: u64) -> u64 {
    let r: u64;
    unsafe { asm!("svc #0", in("x8") n, inlateout("x0") a => r, in("x1") b, in("x2") c) };
    r
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn syscall(n: u64, a: u64, b: u64, c: u64) -> u64 {
    let r: u64;
    unsafe { asm!("syscall", inlateout("rax") n => r, in("rdi") a, in("rsi") b, in("rdx") c, lateout("rcx") _, lateout("r11") _) };
    r
}

pub fn halt(code: u8) -> ! {
    syscall(0, code as u64, 0, 0);
    loop {}
}

/// Write bytes to a file: 1 is the standard output, 2 the standard error.
pub fn write(fd: u32, buf: &[u8]) {
    syscall(2, fd as u64, buf.as_ptr() as u64, buf.len() as u64);
}

/// Show bytes: they are part of what the run is. File 13, as SP1's public values.
pub fn outs(x: &[u8]) {
    write(13, x);
}

/// The next hint vector.
pub fn read_vec() -> Vec<u8> {
    let n = syscall(0xF0, 0, 0, 0) as usize;
    // whole words, and one more than the bytes need: the machine writes that much
    let mut words: Vec<u64> = vec![0; n / 8 + 1];
    syscall(0xF1, words.as_mut_ptr() as u64, n as u64, 0);
    let mut v = Vec::with_capacity(n);
    for k in 0..n {
        v.push((words[k / 8] >> (8 * (k % 8))) as u8);
    }
    v
}

/// A file as a place to format into.
pub struct File(pub u32);

impl Write for File {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        write(self.0, s.as_bytes());
        Ok(())
    }
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {{ use core::fmt::Write; let _ = write!($crate::File(1), $($arg)*); }};
}
#[macro_export]
macro_rules! println {
    ($($arg:tt)*) => {{ use core::fmt::Write; let _ = writeln!($crate::File(1), $($arg)*); }};
}
#[macro_export]
macro_rules! eprintln {
    ($($arg:tt)*) => {{ use core::fmt::Write; let _ = writeln!($crate::File(2), $($arg)*); }};
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    let _ = writeln!(File(2), "{info}");
    halt(1)
}

/// The heap: memory handed out in order and not taken back, but for the last piece.
const HEAP: usize = 32 << 20;
static mut MEMORY: [u8; HEAP] = [0; HEAP];
static mut NEXT: usize = 0;

struct Bump;

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let start = (NEXT + l.align() - 1) & !(l.align() - 1);
        if start + l.size() > HEAP {
            return core::ptr::null_mut();
        }
        NEXT = start + l.size();
        core::ptr::addr_of_mut!(MEMORY).cast::<u8>().add(start)
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        let base = core::ptr::addr_of_mut!(MEMORY).cast::<u8>();
        if p.add(l.size()) == base.add(NEXT) {
            NEXT = p.offset_from(base) as usize;
        }
    }
}

#[global_allocator]
static ALLOCATOR: Bump = Bump;

/// The stack.
const STACK: usize = 4 << 20;
#[no_mangle]
static mut STACK_MEMORY: [u8; STACK] = [0; STACK];

#[cfg(target_arch = "aarch64")]
global_asm!(
    ".section .text.start", ".globl _start", ".type _start, %function", "_start:",
    "adrp x0, STACK_MEMORY", "add x0, x0, :lo12:STACK_MEMORY", "mov x1, #{size}", "add sp, x0, x1",
    "bl guest_start", "1: b 1b", ".size _start, . - _start",
    size = const STACK,
);

#[cfg(target_arch = "x86_64")]
global_asm!(
    ".section .text.start", ".globl _start", ".type _start, @function", "_start:",
    "lea rsp, [rip + STACK_MEMORY + {size}]", "call guest_start", "2: jmp 2b", ".size _start, . - _start",
    size = const STACK,
);

extern "C" {
    fn guest_main();
}

#[no_mangle]
extern "C" fn guest_start() -> ! {
    unsafe { guest_main() };
    halt(0)
}

/// The guest's `main`.
#[macro_export]
macro_rules! entry {
    ($main:path) => {
        #[no_mangle]
        pub extern "C" fn guest_main() {
            $main()
        }
    };
}
