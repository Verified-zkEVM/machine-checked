# Building a Rust program for the proved lift

What to set when you build a `no_std` Rust program, with its own entry, panic handler and
allocator, for `decompile --proved`, and what goes wrong without each setting. Flags do not
reach a prebuilt library: against one (SP1's `std`) the panic, jump-table and inlining items
cover only your own crates. `-Z` flags need nightly, and `-C llvm-args` are LLVM's own options:
check them when the toolchain moves. The figures are from one program of about 230 functions
(198 in its first build), built for RV64IM with Cargo; [`Examples/build.sh`](../Examples/build.sh)
builds through LLVM IR and clang instead, where all but the Cargo items apply.

## What the lift takes

- **RV64IM, static, not stripped, no compressed instructions**, or `decompile` refuses the file
  ([`Tools/README.md`](../Tools/README.md#from-an-elf)). The target `riscv64im-unknown-none-elf`
  gives this, with `-Z build-std=core,alloc` since it has no prebuilt library.
- **Count what is left out first.** `decompile --to lprog --proved` prints how many functions it
  left out (naming each, with the word that excluded it) and how many `abort`s it wrote. Both
  should be zero: an `abort`, which a call into a left-out function also becomes, is a step a
  proof must show is never taken. Our first build left out 109 of 198, 107 for `unimp`.
- **No 32-bit operations the machine does not run.** A function holding one of the nine
  ([list](../Tools/README.md#from-an-elf)) is left out. `u32` and `i32` arithmetic compiles to
  them (a `u32` division gave `divuw`); compute in `u64` where the result is the same.

## Panics and halting

- **`panic = "abort"` with a handler that halts.** Immediate abort (`panic = "immediate-abort"`,
  a nightly Cargo feature) puts an `unimp` at every panic site, which leaves the function out
  ([`ELF.md`](ELF.md#build-switches) proposes it, for a smaller panic runtime; that holds only
  once `unimp` is lifted as a trap, [`Examples/README.md`](../Examples/README.md#what-was-found)
  finding 14). With `panic = "abort"` and a `#[panic_handler]` that halts through `ecall` with
  an exit code that does not accept, every panic path ends in a call to a function that never
  returns: prove its contract once, with postcondition `False` (as `stop_contract` in
  [`Examples/Calls`](../Examples/Calls/RiscV/Proofs.lean)), and `lsym … using` closes each panic
  path at the call. A halt that does not accept is safe for `SafeN`, so no proof has to show a
  panic unreachable.
- **A halt the compiler sees return.** Write the halting `ecall` as an `asm!` without
  `options(noreturn)`, followed by `loop {}`; after a `noreturn` block the compiler writes an
  `unimp`. Library code that calls `abort` itself shows up in the left-out list; replace the
  call (we replaced `core`'s sort).

## Jump tables

- **`-C jump-tables=no`.** The proved lift has no computed jump within a function
  ([#3](https://github.com/Verified-zkEVM/machine-checked/issues/3)): a jump table lifts as a
  tail call to every function (`tail via` and every index, in the Lprog text), and its target,
  inside the function, is none of them, so the function cannot be proved safe.

## Function boundaries

Under fat LTO, LLVM decides which functions exist and what their signatures are. Pin them:

- **Inlining.** Mark the functions you prove by contract `#[inline(never)]` and small
  straight-line helpers `#[inline(always)]`, and keep LLVM's own inlining low for the rest
  (`-C llvm-args=-inline-threshold=25`). Otherwise size decides whether a function exists, and an
  inlined callee is proved again inside every caller: pinning shrank one function from 4,267 to
  697 instructions.
- **No merging.** `-Z merge-functions=disabled`, so that two symbols never share one body (a
  precaution; not measured).
- **No runtime or partial unrolling.** `-C llvm-args=-unroll-runtime=false` and
  `-C llvm-args=-unroll-allow-partial=false`: a loop of variable length stays one loop, with one
  invariant, rather than an unrolled body and a remainder loop.
- **Signatures.** Fat LTO rewrites an internal function's signature for its callers
  (dead-argument elimination, interprocedural constant propagation): a one-line edit to the
  allocator changed 75 of 230 lifted functions, the size moving from `a1` to `a0` at every call.
  Put a function that many proved callers reach, and whose body may change, behind an exported
  C symbol; the same edit then changed 1 (measured; replay it when the toolchain moves):

  ```rust
  #[unsafe(no_mangle)]
  #[inline(never)]
  extern "C" fn bump_alloc(size: usize, align: usize) -> *mut u8 { /* the allocator */ }

  unsafe impl GlobalAlloc for Bump {
      #[inline(always)]
      unsafe fn alloc(&self, l: Layout) -> *mut u8 { bump_alloc(l.size(), l.align()) }
      unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
  }
  ```

  For the same reason, take a contract's argument registers from the lift, not the Rust
  signature.

## A build that is a function of its sources

- **Hermetic flags.** Cargo merges `rustflags` from every `.cargo/config.toml` in the directory
  it runs in and its parents and from `$CARGO_HOME`, and joins `target.<triple>.rustflags` with
  every matching `target.<cfg>.rustflags`. A `[target.'cfg(all())']` entry adding
  `-C target-cpu=native` in a parent directory changed 128 of 230 lifted functions, and the
  build still succeeded. Set `CARGO_ENCODED_RUSTFLAGS` (separator `0x1f`) to your own flags: it
  replaces every `rustflags` entry, your config's included. Other keys (`[profile]`, `[build]`,
  `[env]`) still merge; `cargo config get`, on nightly, shows what is in force. Pin the
  toolchain and `Cargo.lock`; two builds in different directories should give the same bytes.
- **Pin the image.** Lake does not track the ELF that `check_elf_words` reads
  ([`Tools/README.md`](../Tools/README.md#as-lean)), so a rebuilt binary and the proofs can drift
  apart unnoticed. Commit the ELF's sha256 beside the proofs, fail the build when it moves, and
  name it where the top theorem is stated.
- **Debug information.** [`ELF.md`](ELF.md#results-on-zip-2005s-guest-2026-10-12) found that
  every debug level changed an SP1 guest's image; in ours `debug = 1` left `.text` and `.rodata`
  byte-identical, `debug = 2` changed 8 of 229 functions, and `debug = 2` with
  `-Z inline-mir-preserve-debug=no` changed none. Build it as a second build and compare hashes.

## Relocations

- **`--emit-relocs`** (a linker argument, `cargo:rustc-link-arg` in `build.rs`) keeps relocations
  that say which `auipc` starts a call, which forms an address with which later instructions,
  and which data words hold addresses, without changing the loaded image
  ([`ELF.md`](ELF.md#results-on-zip-2005s-guest-2026-10-12)). `decompile` does not read them;
  your own tools then need not guess from instruction patterns.
- **`--no-relax` when objects from clang or assembly are linked in.** rustc's RISC-V targets do
  not enable relaxation, so its calls are `auipc; jalr` whatever their distance; a relaxed call
  makes a function's size, and every address after it, depend on where its callees end up.

## After the build: checks for the kernel

- **`decide` on a `Bool`, not a `Prop`.** State a large closed fact about the image as a `Bool`
  equation, `(xs.all p) = true` or `(a == b) = true`, and prove it by `decide +kernel` or
  `kernel_eq` (`Tools.ToLean`); `List.all_eq_true` gives back the `Prop`. On an equality of two
  lists of `BitVec 64`, `decide` on the `Prop` was still growing at 5.5 GB in the kernel after
  three minutes; the `Bool` form was instant.

A machine that stops on a word it does not decode makes "a run that halts accepting satisfies
P" hold of every run that reaches such a word, while the real machine may run the word and
accept. Besides the witnesses [`CONTRIBUTING.md`](../CONTRIBUTING.md#proofs) asks for:

- **Every code word decodes**, over all the code the machine can fetch, as one `Bool` equation.
  The written `words` hold only the functions the lift took, so read the image's code
  (`gen-image` writes each text symbol's words; code outside a symbol needs your own reader).
- **Run the statement's own machine.** Execute the definitions the theorem is about on real
  inputs and see each verdict: accept on a valid input, reject on a corrupted one.
