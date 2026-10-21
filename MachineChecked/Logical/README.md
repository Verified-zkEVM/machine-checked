# Logical

**Layer 1 of the [roadmap](../../ROADMAP.md): the structured logical program. Not started.**

The ISA-independent layer meant for proving. Registers become variables, stack frames become
locals, and control flow is structured. It is where the program logics go (Hoare,
separation, relational, cost), and where function contracts are stated and composed, with the
calling convention and the execution context as parameters.

Programs arrive here from the low logical program (`../Lprog`, layer 0.5) by decompilation: a
verified lift that rebuilds variables and structured control flow from a function's
control-flow graph. It will not always succeed, so it is per function and may be partial; a
function that cannot be lifted stays at layer 0.5 and is proved there.

A design sketch is in [`docs/LogicalMachine.md`](../../docs/LogicalMachine.md). Contributions
here are welcome: open an issue first to agree on the key definitions (see
[`CONTRIBUTING.md`](../../CONTRIBUTING.md), "Larger contributions").
