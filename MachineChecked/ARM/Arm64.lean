/-
The AArch64 semantics: the trusted package `arm64` of DeepMind's arm64-semantics
(`docs/ISA.md`), used unmodified at the commit pinned in `lakefile.toml`. Its `Arm64.Step`
fetches four bytes, decodes and executes them. Only the trusted package is imported, not its
`ProofLib`, case studies or tests.
-/
import Arm64.Trusted
