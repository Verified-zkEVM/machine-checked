import Cases.Zip2005.Spec.Zip2005.Constants

set_option autoImplicit false

/-!
# § 3.2.1 Note plaintext lead bytes

ZIP 2005 replaces `allowedLeadBytes` so that *Ironwood-pool* note plaintexts admit
**only** lead byte `0x03`, the quantum-recoverable note plaintext version it
introduces. Two further changes are easy to miss: the function no longer depends
on `protocol`, and it never depended on `txVersion` (the argument is retained by
the specification but unused).

The `0x03` claim has a consequence recorded in the ZIP itself: ZIP 226/227 and
ZIP 231 must now pick a different lead byte, because `0x03` is taken.

Reference: <https://zips.z.cash/zip-2005>, § 'Changes to the Protocol
Specification' → § 3.2.1.
-/

namespace Zip2005

/-- The chain value pool a note belongs to. `IronwoodPool` is defined by ZIP 229
and is the pool ZIP 2005 makes recoverable. -/
inductive Pool where
  /-- The Sapling pool. Deliberately *not* given quantum recoverability. -/
  | sapling
  /-- The Orchard pool: existing v5 Orchard notes, not recoverable. -/
  | orchard
  /-- The Ironwood pool (ZIP 229), whose notes are recoverable. -/
  | ironwood
  deriving DecidableEq, Repr

/-- Network-dependent activation parameters. `CanopyActivationHeight` and
`ZIP212GracePeriod` differ between Mainnet and Testnet, so they are parameters
rather than literals: baking in one network's values would make the definition
silently wrong on the other. -/
structure NetworkParams where
  /-- `CanopyActivationHeight`. -/
  canopyActivationHeight : ℕ
  /-- `ZIP212GracePeriod`. -/
  zip212GracePeriod : ℕ

/-- `allowedLeadBytes^pool(height, txVersion)` (§ 3.2.1, as replaced by ZIP 2005).

`txVersion` is in the specification's signature and unused in its definition; it
is kept here for the same reason, so that the transcription can be compared line
for line rather than looking as though a case was dropped. -/
def allowedLeadBytes (np : NetworkParams) (pool : Pool) (height : ℕ)
    (_txVersion : ℕ) : List UInt8 :=
  if height < np.canopyActivationHeight then
    [0x01]
  else if height < np.canopyActivationHeight + np.zip212GracePeriod then
    [0x01, 0x02]
  else if pool ≠ Pool.ironwood then
    [0x02]
  else
    [0x03]

/-- The ZIP's headline consequence: after the ZIP 212 grace period, an
Ironwood-pool note plaintext may carry only lead byte `0x03`. -/
theorem ironwood_leadByte (np : NetworkParams) (height txVersion : ℕ)
    (h : np.canopyActivationHeight + np.zip212GracePeriod ≤ height) :
    allowedLeadBytes np Pool.ironwood height txVersion = [0x03] := by
  have h1 : ¬ height < np.canopyActivationHeight := by omega
  have h2 : ¬ height < np.canopyActivationHeight + np.zip212GracePeriod := by omega
  simp [allowedLeadBytes, h1, h2]

/-- Outside the Ironwood pool nothing changes: the post-grace-period answer is
still `0x02`. This is the half of the replacement that must *not* have moved. -/
theorem non_ironwood_leadByte (np : NetworkParams) (pool : Pool) (height txVersion : ℕ)
    (hpool : pool ≠ Pool.ironwood)
    (h : np.canopyActivationHeight + np.zip212GracePeriod ≤ height) :
    allowedLeadBytes np pool height txVersion = [0x02] := by
  have h1 : ¬ height < np.canopyActivationHeight := by omega
  have h2 : ¬ height < np.canopyActivationHeight + np.zip212GracePeriod := by omega
  simp [allowedLeadBytes, h1, h2, hpool]

/-- Before Canopy the pool is irrelevant, as it is throughout the grace period:
the ZIP's rewrite touches only the post-grace-period case. -/
theorem pre_canopy_leadByte (np : NetworkParams) (pool : Pool) (height txVersion : ℕ)
    (h : height < np.canopyActivationHeight) :
    allowedLeadBytes np pool height txVersion = [0x01] := by
  simp [allowedLeadBytes, h]

end Zip2005
