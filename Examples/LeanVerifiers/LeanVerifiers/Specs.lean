/-
  LeanVerifiers.Specs

  The specifications, from leanEthereum/leanVM#837's package `native`: the models of the Rust
  code and what they are proved equal to. This module imports them and names the statements
  the end theorems will be about, so that a change of them upstream is seen here.

  * `NativeRustc.Xmss.verify_eq`, `NativeRustc.Sphincs.verify_eq`: the byte models of
    `xmss_verify` and `sphincs_verify` are `LeanXmss.verifyWithKeccak` and
    `Sphincs.verifyWithKeccak`.
-/

import NativeRustc.Xmss.Verify
import NativeRustc.Sphincs.Verify

namespace LeanVerifiers

/-- info: 'NativeRustc.Xmss.verify_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustc.Xmss.verify_eq

/-- info: 'NativeRustc.Sphincs.verify_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeRustc.Sphincs.verify_eq

end LeanVerifiers
