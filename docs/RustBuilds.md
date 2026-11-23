# Building a Rust program for the proved lift

What to set when you build a Rust program for `decompile --proved`: which settings decide what
the lift takes, how much of the lifted program moves when the source changes, and how to check
that the theorems are about the binary you ship. Each item says what goes wrong without it.
The figures come from one Rust program of about 230 functions built for RV64IM with Cargo.
[`Examples/build.sh`](../Examples/build.sh) builds the Rust examples another way, through LLVM
IR and clang; all but the Cargo items apply there too.

## What the lift takes

- **RV64IM, static, not stripped, no compressed instructions.** `decompile` refuses compressed
  instructions, position-independent files and stripped files
  ([`Tools/README.md`](../Tools/README.md#from-an-elf)). The target `riscv64im-unknown-none-elf`
  gives this; it has no prebuilt library, so build `core` and `alloc` with
  `-Z build-std=core,alloc` on a pinned nightly.
- **Count what is left out before proving anything.** `decompile --to lprog --proved` prints how
  many functions it left out and how many `abort` instructions it wrote, and names each
  left-out function with the word and address that excluded it. Both counts should be zero: a
  call into a left-out function, like an `abort`, is a step a proof must show is never taken.
  Our first build left out 109 of 198 functions, 107 of them for `unimp`.
- **No 32-bit operations the machine does not run.** A function holding `addw`, `sllw`, `sraw`,
  `sraiw`, `mulw`, `divw`, `divuw`, `remw` or `remuw` is left out, since riscv-zkvm's machine
  has no step for them. `u32` and `i32` arithmetic compiles to these (a `u32` division gave
  `divuw`); compute in `u64` where the result is the same.

## Panics and halting

- **`panic = "abort"` with a handler that halts.** Immediate abort (`panic = "immediate-abort"`,
  a nightly Cargo feature) puts an `unimp` at every panic site, which leaves the function out. With
  `panic = "abort"` and a `#[panic_handler]` that halts through the halting `ecall` with an exit
  code that does not accept, every panic path ends in a call to a function that never returns.
  Prove its contract once, with postcondition `False` (as `stop_contract` in
  [`Examples/Calls`](../Examples/Calls/RiscV/Proofs.lean)), and `lsym … using` closes each panic
  path at the call. A halt that does not accept is safe for `SafeN`, so no proof has to show a
  panic unreachable.
- **A halt the compiler sees return.** Write the halting `ecall` as an `asm!` without
  `options(noreturn)`, followed by `loop {}`; after a `noreturn` block the compiler writes an
  `unimp`. Library code that calls `abort` itself (in our build, `core`'s sort) shows up in the
  left-out list, and the fix is in the source.

## Jump tables

- **`-C jump-tables=no`.** The proved lift has no jump through a computed address within a
  function (#3). A `match` compiled to a jump table lifts as a tail call whose candidates are
  every function (`tail via` followed by every index, in the Lprog text); its target lies inside
  the function and is none of them, so the function cannot be proved safe. Say where the
  theorem is stated that the binary was built without jump tables, since it is not the default
  build.

## Function boundaries

Under fat LTO with one codegen unit, LLVM decides which functions exist and what their
signatures are, and a small edit can change many lifted functions. Pin them:

- **Inlining.** Mark the functions you prove by contract `#[inline(never)]` and small
  straight-line helpers `#[inline(always)]`, and keep LLVM's own inlining low for the rest
  (`-C llvm-args=-inline-threshold=25`). Otherwise size decides whether a function exists, and an
  inlined callee is proved again inside every caller: pinning shrank one function from 4,267 to
  697 instructions.
- **No merging.** `-Z merge-functions=disabled`, so that a function with the same code as
  another keeps its own code instead of becoming an alias of the other.
- **No runtime or partial unrolling.** `-C llvm-args=-unroll-runtime=false` and
  `-C llvm-args=-unroll-allow-partial=false`: a loop of variable length stays one loop, with one
  invariant, rather than an unrolled body and a remainder loop. Loops of constant length still
  unroll fully into straight-line code.
- **Signatures.** Fat LTO's interprocedural passes rewrite an internal function's signature for
  its callers: dead-argument elimination drops an argument no caller needs, and constant
  propagation folds in an argument every caller passes alike. After a one-line edit to the
  allocator, dead-argument elimination changed 75 of 230 lifted functions (the size moved from
  `a1` to `a0` at every call site). Put a function that many proved callers reach, and whose body
  may change, behind an exported C symbol, whose signature these passes leave alone; the same
  edit then changed 1:

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

  Turning LTO off, or these passes off for the whole image
  (`-C llvm-args=-opt-disable=deadargelim,ipsccp`), also confined the edit, at 2.9% to 45% more
  code. For the same reason, read a function's argument registers off its lift before writing
  its contract: they are the machine function's, not the Rust signature's.

## A build that is a function of its sources

- **Hermetic flags.** Cargo merges `rustflags` from every `.cargo/config.toml` in the build
  directory and its parents and from `$CARGO_HOME`, and joins `target.<triple>.rustflags` with
  every matching `target.<cfg>.rustflags`. A `[target.'cfg(all())']` entry adding
  `-C target-cpu=native` in a parent directory changed 128 of 230 lifted functions, and the
  build still succeeded. Set `CARGO_ENCODED_RUSTFLAGS` (flags separated by `0x1f`), which
  replaces all of them, pin the toolchain in `rust-toolchain.toml`, commit `Cargo.lock`, and
  build into an empty target directory. Two builds in different directories should give the
  same bytes.
- **Pin the image.** `check_elf_words` reads the ELF when the words module is built, and Lake
  does not track the ELF ([`Tools/README.md`](../Tools/README.md#as-lean)), so a rebuilt binary
  and the proofs can drift apart unnoticed. Commit the ELF's sha256 beside the proofs, have the
  build script recompute it and fail when it moves, and name it where the top theorem is stated.
- **Debug information.** Whether it changes the code depends on the toolchain:
  [`ELF.md`](ELF.md#0-summary) found that every debug level changed an SP1 guest's image, while
  in our build `debug = 1` left `.text` and `.rodata` byte-identical, `debug = 2` changed 8 of
  229 functions, and `debug = 2` with `-Z inline-mir-preserve-debug=no` was byte-identical again.
  To use debug information as a hint for proofs, build it as a second build and compare the
  hashes of its sections with the image's.

## Relocations

- **`--emit-relocs` and `--no-relax`**, as linker arguments (for example `cargo:rustc-link-arg`
  in `build.rs`). The retained relocations say exactly which `auipc` starts a call and which
  forms an address with which later instructions, and which data words hold addresses, so a tool
  reading the image does not guess from instruction patterns; the loaded image does not change
  ([`ELF.md`](ELF.md#0-summary)). Without relaxation every call stays `auipc; jalr` whatever its
  distance, so a function's size, and the address of every function after it, does not depend
  on where its callees end up.

## Closed facts for the kernel

- **`decide` on a `Bool`, not a `Prop`.** State a large closed fact about the image as a `Bool`
  equation, `(xs.all p) = true` or `(a == b) = true`, and prove it by `decide +kernel` or
  `kernel_eq` (`Tools.ToLean`); `List.all_eq_true` gives back the `Prop`. `decide` on the `Prop`
  goes through `Decidable` instances: on an equality of two lists of `BitVec 64` the kernel was
  still growing at 5.5 GB after three minutes, while the `Bool` form was instant.

## Non-vacuity

If the machine of your top theorem stops on a word that does not decode, a theorem of the form
"a run that halts accepting satisfies P" says nothing about a run that reaches such a word, and
nothing at all if every run does, while a machine that runs the word may go on and accept.
Besides the witness for every premise that [`CONTRIBUTING.md`](../CONTRIBUTING.md#proofs) asks
for:

- **Every code word decodes.** State it over all the code the machine can fetch, as one `Bool`
  equation the kernel evaluates. The written `words` hold only the functions the lift took, so
  the check must read the image's code, not `words`.
- **Run the statement's own machine.** Execute the definitions the theorem is about on real
  inputs and see each verdict: accept on a valid input, reject on a corrupted one.
