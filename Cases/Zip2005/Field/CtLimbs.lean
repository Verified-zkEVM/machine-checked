import Cases.Zip2005.Field.Limbs
import Cases.Zip2005.Kit.Bytes

/-!
# `CtOption<T>` for a four-limb `T`

`subtle`'s `CtOption::map` selects between `T::default()` and the value under `is_some`;
compiled, that is `limb &&& -is_some` per limb, with `is_some` in byte 0 of the fifth word.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel AsmVerif.RiscV.Sym

/-- The five words of a `CtOption<T>` with `is_some = c`: the limbs `L` masked by `c`, and
`is_some` written into byte 0 of the fifth word `o4`. -/
def ctLimbs (c : Prop) [Decidable c] (L : List Word) (o4 : Word) : List Word :=
  L.map (fun w => if c then w else 0#64) ++ [replaceByte o4 0 (if c then 1#8 else 0#8)]

theorem ctLimbs_four (c : Prop) [Decidable c] (a b d e o4 : Word) :
    ctLimbs c [a, b, d, e] o4 =
      [if c then a else 0#64, if c then b else 0#64, if c then d else 0#64, if c then e else 0#64,
        replaceByte o4 0 (if c then 1#8 else 0#8)] := rfl

theorem natToLeLimbs_four (x : Nat) :
    natToLeLimbs 4 x =
      [BitVec.ofNat 64 x, BitVec.ofNat 64 (x >>> 64), BitVec.ofNat 64 (x >>> 128),
        BitVec.ofNat 64 (x >>> 192)] := rfl

end Cases.Zip2005
