1. Which spec counts as the official one for x86 and ARM. ISA.md says "Kraken probably?" for x86 and "?" for ARM. Sail has models for both: ARM's comes from Arm's own ASL spec, and there is a Sail x86 model. You already have a pipeline that turns Sail into Lean for RISC-V, so using Sail for all three would make "verified against the official spec" mean the same thing on every ISA. The cost is that the x86 and ARM Sail models are very large.


2. What exactly needs to be generic. riscv-decomp already defines a Stepper interface that ZisK and SP1 plug into. One option is to make that the ISA-independent core, so each ISA only supplies a stepper, instruction specs and an equivalence proof. Then the triples, loop rules, Tailrec, the certificate and refinement are written once. How much of the CFG and body extractor can be shared across ISAs is the open question.
   *Answered (2026-10-20):* `riscv-decomp` is dropped. The ISA-generic core is CatCrypt's `Isa`/`IsaMachine`, ported, with riscv-zkvm's `stepSp1` as the RISC-V instance (`CATCRYPT-PORT.md` P2).


3. How "Ascent" fits in. The README says you want to stay compatible with sgraf812/ascent indefinitely, and catcrypt also has an Ascent namespace. Is Ascent the decompilation layer you build on, or a peer approach whose interfaces you want to match?
   *Answered (2026-10-20):* we build on it. CatCrypt's Ascent descends from sgraf812/ascent, and its `CorresIsa` is ported as our ascent (`CATCRYPT-PORT.md`).


4. Where the trust boundary sits around the ELF. In zip-2005 the hardest part turned out to be the runtime underneath the program: contracts, panic paths, statics and the heap. That made the top-level theorem vacuous until those contracts are restated. A generic ELF layer will need a principled way to state and check runtime and ABI assumptions, or each new binary will hit the same problem.



5. Scope of the first milestone. Doing RISC-V end to end first seems like the obvious choice, since nearly every piece already exists. Then you'd generalize once a second ISA forces the abstractions.
