/-
  Cases.Zip2005.Top.Load

  The image facts the top-level theorem takes, as theorems about the loaded image
  (`Cases.Zip2005.Image.Layout.image`, read by `AsmVerif.RiscV.Load` and cross-checked against
  riscv-zkvm's own loader by `gen-image`): the code of every function the proofs step
  (`RunCode.of_image`), the code window, the read-only segment (`roImage`), the `.data`/`.bss`
  words `guest_elf_run` reads, and the entry point. Nothing here is evaluated by a tool at run
  time; each fact is kernel-checked once, against the generated image data.
-/

import Cases.Zip2005.Image
import Cases.Zip2005.Loaded
import Cases.Zip2005.Top.Assumptions
import AsmVerif.RiscV.Sym.Load

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Sym Cases.Zip2005.Image

noncomputable abbrev image : Image := Layout.image

/-- The start state of a run over the loaded image with private input `I`. -/
noncomputable abbrev start (I : List (BitVec 8)) : MachineState := image.state I

theorem start_code (I : List (BitVec 8)) : (start I).code = image.codeAt := rfl
theorem start_pc (I : List (BitVec 8)) : (start I).pc = 0x7801bcd0#64 := rfl
theorem start_input (I : List (BitVec 8)) : (start I).privateInput = I := rfl
theorem start_getMem (I : List (BitVec 8)) (a : Word) : (start I).getMem a = image.memAt a := rfl

/-! ## Code -/

set_option maxRecDepth 10000 in
/-- Every function the proofs step is loaded at its address, and the code map is confined to
    the text window. -/
theorem RunCode.of_image {s : MachineState} (hs : s.code = image.codeAt) : RunCode s where
  hc_78016938 := codeAt_of_image Loaded.codeWF Layout.code_F_78016938 F_78016938.decode_ok hs
  hc_7801775c := codeAt_of_image Loaded.codeWF Layout.code_F_7801775c F_7801775c.decode_ok hs
  hc_7801806c := codeAt_of_image Loaded.codeWF Layout.code_F_7801806c F_7801806c.decode_ok hs
  hc_7801823c := codeAt_of_image Loaded.codeWF Layout.code_F_7801823c F_7801823c.decode_ok hs
  hc_780191c4 := codeAt_of_image Loaded.codeWF Layout.code_F_780191c4 F_780191c4.decode_ok hs
  hc_780197cc := codeAt_of_image Loaded.codeWF Layout.code_F_780197cc F_780197cc.decode_ok hs
  hc_78019918 := codeAt_of_image Loaded.codeWF Layout.code_F_78019918 F_78019918.decode_ok hs
  hc_78019a10 := codeAt_of_image Loaded.codeWF Layout.code_F_78019a10 F_78019a10.decode_ok hs
  hc_78019b50 := codeAt_of_image Loaded.codeWF Layout.code_F_78019b50 F_78019b50.decode_ok hs
  hc_78019bf0 := codeAt_of_image Loaded.codeWF Layout.code_F_78019bf0 F_78019bf0.decode_ok hs
  hc_78019cb8 := codeAt_of_image Loaded.codeWF Layout.code_F_78019cb8 F_78019cb8.decode_ok hs
  hc_78019dd8 := codeAt_of_image Loaded.codeWF Layout.code_F_78019dd8 F_78019dd8.decode_ok hs
  hc_78019f50 := codeAt_of_image Loaded.codeWF Layout.code_F_78019f50 F_78019f50.decode_ok hs
  hc_78019ff4 := codeAt_of_image Loaded.codeWF Layout.code_F_78019ff4 F_78019ff4.decode_ok hs
  hc_7801aed0 := codeAt_of_image Loaded.codeWF Layout.code_F_7801aed0 F_7801aed0.decode_ok hs
  hc_7801b4d8 := codeAt_of_image Loaded.codeWF Layout.code_F_7801b4d8 F_7801b4d8.decode_ok hs
  hc_7801beb0 := codeAt_of_image Loaded.codeWF Layout.code_F_7801beb0 F_7801beb0.decode_ok hs
  hc_7801bf3c := codeAt_of_image Loaded.codeWF Layout.code_F_7801bf3c F_7801bf3c.decode_ok hs
  hc_7801bf4c := codeAt_of_image Loaded.codeWF Layout.code_F_7801bf4c F_7801bf4c.decode_ok hs
  hc_7801bf5c := codeAt_of_image Loaded.codeWF Layout.code_F_7801bf5c F_7801bf5c.decode_ok hs
  hc_7801cb44 := codeAt_of_image Loaded.codeWF Layout.code_F_7801cb44 F_7801cb44.decode_ok hs
  hc_7801ce6c := codeAt_of_image Loaded.codeWF Layout.code_F_7801ce6c F_7801ce6c.decode_ok hs
  hc_7801ce90 := codeAt_of_image Loaded.codeWF Layout.code_F_7801ce90 F_7801ce90.decode_ok hs
  hc_7801d074 := codeAt_of_image Loaded.codeWF Layout.code_F_7801d074 F_7801d074.decode_ok hs
  hc_7801d098 := codeAt_of_image Loaded.codeWF Layout.code_F_7801d098 F_7801d098.decode_ok hs
  hc_7801d2c8 := codeAt_of_image Loaded.codeWF Layout.code_F_7801d2c8 F_7801d2c8.decode_ok hs
  hc_7801d2ec := codeAt_of_image Loaded.codeWF Layout.code_F_7801d2ec F_7801d2ec.decode_ok hs
  hc_7801d360 := codeAt_of_image Loaded.codeWF Layout.code_F_7801d360 F_7801d360.decode_ok hs
  hc_7801d3d4 := codeAt_of_image Loaded.codeWF Layout.code_F_7801d3d4 F_7801d3d4.decode_ok hs
  hc_7801d51c := codeAt_of_image Loaded.codeWF Layout.code_F_7801d51c F_7801d51c.decode_ok hs
  hc_7801d92c := codeAt_of_image Loaded.codeWF Layout.code_F_7801d92c F_7801d92c.decode_ok hs
  hc_7801ddd8 := codeAt_of_image Loaded.codeWF Layout.code_F_7801ddd8 F_7801ddd8.decode_ok hs
  hc_7801e26c := codeAt_of_image Loaded.codeWF Layout.code_F_7801e26c F_7801e26c.decode_ok hs
  hc_7801e704 := codeAt_of_image Loaded.codeWF Layout.code_F_7801e704 F_7801e704.decode_ok hs
  hc_7801ed68 := codeAt_of_image Loaded.codeWF Layout.code_F_7801ed68 F_7801ed68.decode_ok hs
  hc_7801f120 := codeAt_of_image Loaded.codeWF Layout.code_F_7801f120 F_7801f120.decode_ok hs
  hc_7801f5a4 := codeAt_of_image Loaded.codeWF Layout.code_F_7801f5a4 F_7801f5a4.decode_ok hs
  hc_7801f780 := codeAt_of_image Loaded.codeWF Layout.code_F_7801f780 F_7801f780.decode_ok hs
  hc_7801fb1c := codeAt_of_image Loaded.codeWF Layout.code_F_7801fb1c F_7801fb1c.decode_ok hs
  hc_7801fbcc := codeAt_of_image Loaded.codeWF Layout.code_F_7801fbcc F_7801fbcc.decode_ok hs
  hc_7802018c := codeAt_of_image Loaded.codeWF Layout.code_F_7802018c F_7802018c.decode_ok hs
  hc_780203dc := codeAt_of_image Loaded.codeWF Layout.code_F_780203dc F_780203dc.decode_ok hs
  hc_78020548 := codeAt_of_image Loaded.codeWF Layout.code_F_78020548 F_78020548.decode_ok hs
  hc_780207e8 := codeAt_of_image Loaded.codeWF Layout.code_F_780207e8 F_780207e8.decode_ok hs
  hc_78020ca0 := codeAt_of_image Loaded.codeWF Layout.code_F_78020ca0 F_78020ca0.decode_ok hs
  hc_78020d50 := codeAt_of_image Loaded.codeWF Layout.code_F_78020d50 F_78020d50.decode_ok hs
  hc_78021238 := codeAt_of_image Loaded.codeWF Layout.code_F_78021238 F_78021238.decode_ok hs
  hc_7802233c := codeAt_of_image Loaded.codeWF Layout.code_F_7802233c F_7802233c.decode_ok hs
  hc_78022514 := codeAt_of_image Loaded.codeWF Layout.code_F_78022514 F_78022514.decode_ok hs
  hc_780227b4 := codeAt_of_image Loaded.codeWF Layout.code_F_780227b4 F_780227b4.decode_ok hs
  hc_78022848 := codeAt_of_image Loaded.codeWF Layout.code_F_78022848 F_78022848.decode_ok hs
  hc_78022a74 := codeAt_of_image Loaded.codeWF Layout.code_F_78022a74 F_78022a74.decode_ok hs
  hc_78022ca0 := codeAt_of_image Loaded.codeWF Layout.code_F_78022ca0 F_78022ca0.decode_ok hs
  hc_78022f5c := codeAt_of_image Loaded.codeWF Layout.code_F_78022f5c F_78022f5c.decode_ok hs
  hc_780231e8 := codeAt_of_image Loaded.codeWF Layout.code_F_780231e8 F_780231e8.decode_ok hs
  hc_78023230 := codeAt_of_image Loaded.codeWF Layout.code_F_78023230 F_78023230.decode_ok hs
  hc_78023278 := codeAt_of_image Loaded.codeWF Layout.code_F_78023278 F_78023278.decode_ok hs
  hc_780232f4 := codeAt_of_image Loaded.codeWF Layout.code_F_780232f4 F_780232f4.decode_ok hs
  hc_78023308 := codeAt_of_image Loaded.codeWF Layout.code_F_78023308 F_78023308.decode_ok hs
  hc_7802340c := codeAt_of_image Loaded.codeWF Layout.code_F_7802340c F_7802340c.decode_ok hs
  hc_780234cc := codeAt_of_image Loaded.codeWF Layout.code_F_780234cc F_780234cc.decode_ok hs
  hc_78023544 := codeAt_of_image Loaded.codeWF Layout.code_F_78023544 F_78023544.decode_ok hs
  hc_78023594 := codeAt_of_image Loaded.codeWF Layout.code_F_78023594 F_78023594.decode_ok hs
  hc_780235e8 := codeAt_of_image Loaded.codeWF Layout.code_F_780235e8 F_780235e8.decode_ok hs
  hc_780237dc := codeAt_of_image Loaded.codeWF Layout.code_F_780237dc F_780237dc.decode_ok hs
  hc_78023864 := codeAt_of_image Loaded.codeWF Layout.code_F_78023864 F_78023864.decode_ok hs
  hc_780239bc := codeAt_of_image Loaded.codeWF Layout.code_F_780239bc F_780239bc.decode_ok hs
  hc_78023a18 := codeAt_of_image Loaded.codeWF Layout.code_F_78023a18 F_78023a18.decode_ok hs
  hc_78023d7c := codeAt_of_image Loaded.codeWF Layout.code_F_78023d7c F_78023d7c.decode_ok hs
  hc_78023ec4 := codeAt_of_image Loaded.codeWF Layout.code_F_78023ec4 F_78023ec4.decode_ok hs
  hc_78023f64 := codeAt_of_image Loaded.codeWF Layout.code_F_78023f64 F_78023f64.decode_ok hs
  hc_7802413c := codeAt_of_image Loaded.codeWF Layout.code_F_7802413c F_7802413c.decode_ok hs
  hc_78025164 := codeAt_of_image Loaded.codeWF Layout.code_F_78025164 F_78025164.decode_ok hs
  hc_78025654 := codeAt_of_image Loaded.codeWF Layout.code_F_78025654 F_78025654.decode_ok hs
  hc_78025854 := codeAt_of_image Loaded.codeWF Layout.code_F_78025854 F_78025854.decode_ok hs
  hc_78025a1c := codeAt_of_image Loaded.codeWF Layout.code_F_78025a1c F_78025a1c.decode_ok hs
  hc_78026258 := codeAt_of_image Loaded.codeWF Layout.code_F_78026258 F_78026258.decode_ok hs
  hc_78026878 := codeAt_of_image Loaded.codeWF Layout.code_F_78026878 F_78026878.decode_ok hs
  hc_78026928 := codeAt_of_image Loaded.codeWF Layout.code_F_78026928 F_78026928.decode_ok hs
  hc_78026b44 := codeAt_of_image Loaded.codeWF Layout.code_F_78026b44 F_78026b44.decode_ok hs
  hc_7802827c := codeAt_of_image Loaded.codeWF Layout.code_F_7802827c F_7802827c.decode_ok hs
  hc_78028298 := codeAt_of_image Loaded.codeWF Layout.code_F_78028298 F_78028298.decode_ok hs
  hc_78028718 := codeAt_of_image Loaded.codeWF Layout.code_F_78028718 F_78028718.decode_ok hs
  hc_78028b34 := codeAt_of_image Loaded.codeWF Layout.code_F_78028b34 F_78028b34.decode_ok hs
  hc_78028ce8 := codeAt_of_image Loaded.codeWF Layout.code_F_78028ce8 F_78028ce8.decode_ok hs
  hc_78028d04 := codeAt_of_image Loaded.codeWF Layout.code_F_78028d04 F_78028d04.decode_ok hs
  hc_78029468 := codeAt_of_image Loaded.codeWF Layout.code_F_78029468 F_78029468.decode_ok hs
  hc_780297c0 := codeAt_of_image Loaded.codeWF Layout.code_F_780297c0 F_780297c0.decode_ok hs
  hc_78029ae8 := codeAt_of_image Loaded.codeWF Layout.code_F_78029ae8 F_78029ae8.decode_ok hs
  hc_78029b18 := codeAt_of_image Loaded.codeWF Layout.code_F_78029b18 F_78029b18.decode_ok hs
  hc_78029b64 := codeAt_of_image Loaded.codeWF Layout.code_F_78029b64 F_78029b64.decode_ok hs
  hc_78029d94 := codeAt_of_image Loaded.codeWF Layout.code_F_78029d94 F_78029d94.decode_ok hs
  hc_7802e2b4 := codeAt_of_image Loaded.codeWF Layout.code_F_7802e2b4 F_7802e2b4.decode_ok hs
  hc_7802e5b4 := codeAt_of_image Loaded.codeWF Layout.code_F_7802e5b4 F_7802e5b4.decode_ok hs
  hc_7802e8ec := codeAt_of_image Loaded.codeWF Layout.code_F_7802e8ec F_7802e8ec.decode_ok hs
  hc_7802e9b8 := codeAt_of_image Loaded.codeWF Layout.code_F_7802e9b8 F_7802e9b8.decode_ok hs
  hc_7802ed10 := codeAt_of_image Loaded.codeWF Layout.code_F_7802ed10 F_7802ed10.decode_ok hs
  hc_7802f038 := codeAt_of_image Loaded.codeWF Layout.code_F_7802f038 F_7802f038.decode_ok hs
  hc_7802f358 := codeAt_of_image Loaded.codeWF Layout.code_F_7802f358 F_7802f358.decode_ok hs
  hc_780315c0 := codeAt_of_image Loaded.codeWF Layout.code_F_780315c0 F_780315c0.decode_ok hs
  hc_78031be8 := codeAt_of_image Loaded.codeWF Layout.code_F_78031be8 F_78031be8.decode_ok hs
  hc_78032c1c := codeAt_of_image Loaded.codeWF Layout.code_F_78032c1c F_78032c1c.decode_ok hs
  hc_78032db4 := codeAt_of_image Loaded.codeWF Layout.code_F_78032db4 F_78032db4.decode_ok hs
  hc_78032fa4 := codeAt_of_image Loaded.codeWF Layout.code_F_78032fa4 F_78032fa4.decode_ok hs
  hc_78033260 := codeAt_of_image Loaded.codeWF Layout.code_F_78033260 F_78033260.decode_ok hs
  hc_78035f88 := codeAt_of_image Loaded.codeWF Layout.code_F_78035f88 F_78035f88.decode_ok hs
  hc_78035fe0 := codeAt_of_image Loaded.codeWF Layout.code_F_78035fe0 F_78035fe0.decode_ok hs
  hc_780360c8 := codeAt_of_image Loaded.codeWF Layout.code_F_780360c8 F_780360c8.decode_ok hs
  hc_780360e0 := codeAt_of_image Loaded.codeWF Layout.code_F_780360e0 F_780360e0.decode_ok hs
  hc_7803a0fc := codeAt_of_image Loaded.codeWF Layout.code_F_7803a0fc F_7803a0fc.decode_ok hs
  hc_7803a110 := codeAt_of_image Loaded.codeWF Layout.code_F_7803a110 F_7803a110.decode_ok hs
  hc_7803dd28 := codeAt_of_image Loaded.codeWF Layout.code_F_7803dd28 F_7803dd28.decode_ok hs
  hc_7803f54c := codeAt_of_image Loaded.codeWF Layout.code_F_7803f54c F_7803f54c.decode_ok hs
  hc_7803f57c := codeAt_of_image Loaded.codeWF Layout.code_F_7803f57c F_7803f57c.decode_ok hs
  hc_7801cac0 := codeAt_of_image Loaded.codeWF Layout.code_F_7801cac0 F_7801cac0.decode_ok hs
  hc_7801cdb4 := codeAt_of_image Loaded.codeWF Layout.code_F_7801cdb4 F_7801cdb4.decode_ok hs
  hc_78023cbc := codeAt_of_image Loaded.codeWF Layout.code_F_78023cbc F_78023cbc.decode_ok hs
  hc_7801e110 := codeAt_of_image Loaded.codeWF Layout.code_F_7801e110 F_7801e110.decode_ok hs
  hc_78021e7c := codeAt_of_image Loaded.codeWF Layout.code_F_78021e7c F_78021e7c.decode_ok hs
  hc_780221a4 := codeAt_of_image Loaded.codeWF Layout.code_F_780221a4 F_780221a4.decode_ok hs
  hc_7802225c := codeAt_of_image Loaded.codeWF Layout.code_F_7802225c F_7802225c.decode_ok hs
  hc_7801dfb4 := codeAt_of_image Loaded.codeWF Layout.code_F_7801dfb4 F_7801dfb4.decode_ok hs
  hc_78021720 := codeAt_of_image Loaded.codeWF Layout.code_F_78021720 F_78021720.decode_ok hs
  hcw := codeWithin_of_image Loaded.codeWF (by decide +kernel) (by decide +kernel) hs

/-! ## Memory -/

/-- The read-only segment, as the layout's chunks. -/
theorem roImage {s : MachineState} (hs : ∀ a, s.getMem a = image.memAt a) : RoImage Ro.layout s :=
  roImage_of_image Loaded.dataWF Ro.layout (k := Ro.roIdx) rfl rfl Ro.roChunk_eq hs

/-- A doubleword of the `.data`/`.bss` segment (data chunk 2). -/
theorem memAt_data2 (j : Nat) (hj : j < Data_2.chunk.size) :
    image.memAt (Data_2.chunk.base + BitVec.ofNat 64 (8 * j)) = Data_2.chunk.wordAt j :=
  Image.memAt_chunk (k := 2) Loaded.dataWF rfl hj

/-- One `.data`/`.bss` word, as a region of the start state: cell `j` of data chunk 2 is at
    `a` and holds `v`. -/
theorem data2_word (I : List (BitVec 8)) (j : Nat) (hj : j < Data_2.chunk.size) {a v : Word}
    (ha : Data_2.chunk.base + BitVec.ofNat 64 (8 * j) = a) (hv : Data_2.chunk.wordAt j = v) :
    Region a [v] (start I) := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  obtain rfl : i = 0 := by omega
  rw [start_getMem, show a + BitVec.ofNat 64 (8 * 0) = a by simp, ← ha, memAt_data2 j hj, hv]
  rfl

end Cases.Zip2005.Top
