import Cases.Zip2005.Main.MainSegA0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# The top-level theorem

An accepting SP1 run of the guest from `main`'s entry implies `Cases.Zip2005.Top.GuestAccepts` of the
private input: the two records decode (`Decodes`) to typed values satisfying
`Zip2005.GuestStatement`. The hypotheses are `main_spec`'s: the loaded image, the entry state
(with `FP_TABLES` uninitialised: the first decompression builds it), the runtime contracts and
the panic and reject-halt paths. `main`'s return
continuation is discharged by `AsmVerif.RiscV.SafeN.of_true`: the fact it carries *is* the conclusion.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- **The top-level theorem.** From `main`'s entry, every accepting run of the guest on private
    input `I` establishes `GuestAccepts I`: `I`'s instance and witness records decode to typed
    values satisfying `Zip2005.GuestStatement`.

    The hypotheses come in five groups, each introduced by a heading below:
    * the entry state of `main` (its pc, registers, stack, input, hint area, heap);
    * the loaded code (`hc_<addr>`, one per function the proof steps through);
    * `FP_TABLES`, uninitialised, with the allocator's contracts for building it;
    * the panic and reject paths, which never accept: the only hypotheses `Top/Guest.lean`'s
      `guest_run` leaves assumed;
    * the allocator and runtime contracts at their call sites.

    Everything but the panic and reject paths is discharged from the ELF image in
    `Top/Assumptions`, `Top/Elf`, `Top/Loaded` and `Top/Guest`. -/
theorem guest_accepting_run
    -- `G`: an invariant of the run that every state is assumed to satisfy (`SafeN` only speaks
    -- of runs whose states all satisfy it). The theorem holds for *every* `G`, so it can be taken
    -- to be `fun _ => True`.
    {G : MachineState → Prop}
    -- `nb`: the step bound. `SafeN G nb P s` speaks of accepting runs of fewer than `nb` steps;
    -- the theorem holds for every `nb`, i.e. for runs of any length (partial correctness).
    {nb : Nat}
    -- `L`: the heap's live allocations at `main`'s entry, as (pointer, size in doublewords)
    -- pairs. At the ELF's entry it is `[]` (`Top/Assumptions`'s `MainAssumptions.hheap`).
    {L : List (Word × Nat)}

    /- ### The entry state of `main` -/
    -- `s`: the machine state at `main`'s first instruction.
    (s : MachineState)
    -- `ra`: `main`'s return address; `sp`: the stack pointer at entry; `b`: the hint-area
    -- pointer (the value stored at `0x78040618`, where SP1's `read_vec_raw` places the next record).
    (ra sp b : Word)
    -- `I`: the private input stream (SP1's hint bytes): the instance and witness records.
    (I : List (BitVec 8))
    -- The run starts at `main` (`0x78019ff4`).
    (hpc : s.pc = 0x78019ff4#64)

    /- ### The loaded code

      `hc_<addr>`: the function at `<addr>` is loaded at its address, decoded as the
      instructions in `Image/F_<addr>.lean`. All are proved from the ELF image by
      `Top/Load`'s `RunCode.of_image`. -/
    -- `<bincode::Deserializer as serde::Deserializer>::deserialize_tuple`
    (hc_78016938 : CodeAt F_78016938.base F_78016938.prog s)
    -- `<bincode::Deserializer as serde::Deserializer>::deserialize_tuple`
    (hc_7801775c : CodeAt F_7801775c.base F_7801775c.prog s)
    -- `<bincode::Deserializer as serde::Deserializer>::deserialize_option`
    (hc_7801806c : CodeAt F_7801806c.base F_7801806c.prog s)
    -- `<bincode::Deserializer as serde::Deserializer>::deserialize_struct`
    (hc_7801823c : CodeAt F_7801823c.base F_7801823c.prog s)
    -- `<bincode::Deserializer as serde::Deserializer>::deserialize_struct`
    (hc_780191c4 : CodeAt F_780191c4.base F_780191c4.prog s)
    -- `<bincode tuple Access as serde::SeqAccess>::next_element`
    (hc_780197cc : CodeAt F_780197cc.base F_780197cc.prog s)
    -- `<bincode tuple Access as serde::SeqAccess>::next_element`
    (hc_78019918 : CodeAt F_78019918.base F_78019918.prog s)
    -- `<bincode tuple Access as serde::SeqAccess>::next_element`
    (hc_78019a10 : CodeAt F_78019a10.base F_78019a10.prog s)
    -- `<bincode tuple Access as serde::SeqAccess>::next_element`
    (hc_78019b50 : CodeAt F_78019b50.base F_78019b50.prog s)
    -- `<bincode tuple Access as serde::SeqAccess>::next_element`
    (hc_78019bf0 : CodeAt F_78019bf0.base F_78019bf0.prog s)
    -- `<bincode tuple Access as serde::SeqAccess>::next_element`
    (hc_78019cb8 : CodeAt F_78019cb8.base F_78019cb8.prog s)
    -- `<bool as serde::Deserialize>::deserialize`
    (hc_78019dd8 : CodeAt F_78019dd8.base F_78019dd8.prog s)
    -- `<Box<bincode::ErrorKind> as serde::de::Error>::invalid_length`
    (hc_78019f50 : CodeAt F_78019f50.base F_78019f50.prog s)
    -- `main` — the guest's entry point (`hpc` starts the run here)
    (hc_78019ff4 : CodeAt F_78019ff4.base F_78019ff4.prog s)
    -- `__rustc::__rust_no_alloc_shim_is_unstable_v2` — the allocator shim's marker routine
    (hc_7801aed0 : CodeAt F_7801aed0.base F_7801aed0.prog s)
    -- `memcpy`
    (hc_7801b4d8 : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    -- `read_vec_raw` — SP1: reads the next private-input record from the hint area
    (hc_7801beb0 : CodeAt F_7801beb0.base F_7801beb0.prog s)
    -- `syscall_pallas_add`
    (hc_7801bf3c : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    -- `syscall_pallas_double`
    (hc_7801bf4c : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    -- `syscall_uint256_mulmod`
    (hc_7801bf5c : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    -- `zip_2005_lib::Zip2005Instance::parse_rk`
    (hc_7801cb44 : CodeAt F_7801cb44.base F_7801cb44.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_rivk`
    (hc_7801ce6c : CodeAt F_7801ce6c.base F_7801ce6c.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_alpha`
    (hc_7801ce90 : CodeAt F_7801ce90.base F_7801ce90.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_rivk_ext`
    (hc_7801d074 : CodeAt F_7801d074.base F_7801d074.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_merkle_path`
    (hc_7801d098 : CodeAt F_7801d098.base F_7801d098.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_nk`
    (hc_7801d2c8 : CodeAt F_7801d2c8.base F_7801d2c8.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_g_d`
    (hc_7801d2ec : CodeAt F_7801d2ec.base F_7801d2ec.prog s)
    -- `zip_2005_lib::Zip2005Witness::parse_rho`
    (hc_7801d360 : CodeAt F_7801d360.base F_7801d360.prog s)
    -- `prf_expand::PrfExpand::apply`
    (hc_7801d3d4 : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    -- `note::RandomSeed::psi`
    (hc_7801d51c : CodeAt F_7801d51c.base F_7801d51c.prog s)
    -- `note::RandomSeed::rcm_v3`
    (hc_7801d92c : CodeAt F_7801d92c.base F_7801d92c.prog s)
    -- `tree::MerkleHashOrchard::from_bytes`
    (hc_7801ddd8 : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    -- `halo2_poseidon::poseidon_sponge`
    (hc_7801e26c : CodeAt F_7801e26c.base F_7801e26c.prog s)
    -- `halo2_poseidon::permute::{closure}`
    (hc_7801e704 : CodeAt F_7801e704.base F_7801e704.prog s)
    -- `halo2_poseidon::permute::{closure}`
    (hc_7801ed68 : CodeAt F_7801ed68.base F_7801ed68.prog s)
    -- `halo2_poseidon::permute::{closure}`
    (hc_7801f120 : CodeAt F_7801f120.base F_7801f120.prog s)
    -- `nullifier::Nullifier::from_bytes`
    (hc_7801f5a4 : CodeAt F_7801f5a4.base F_7801f5a4.prog s)
    -- `nullifier::Nullifier::derive`
    (hc_7801f780 : CodeAt F_7801f780.base F_7801f780.prog s)
    -- `spec::NonIdentityPallasPoint::from_bytes`
    (hc_7801fb1c : CodeAt F_7801fb1c.base F_7801fb1c.prog s)
    -- `commitment::NoteCommitment::derive`
    (hc_7801fbcc : CodeAt F_7801fbcc.base F_7801fbcc.prog s)
    -- `spec::NonZeroPallasScalar::from_bytes`
    (hc_7802018c : CodeAt F_7802018c.base F_7802018c.prog s)
    -- `orchard::spec::commit_ivk`
    (hc_780203dc : CodeAt F_780203dc.base F_780203dc.prog s)
    -- `orchard::spec::cached_commit_domain`
    (hc_78020548 : CodeAt F_78020548.base F_78020548.prog s)
    -- `orchard::spec::prf_nf`
    (hc_780207e8 : CodeAt F_780207e8.base F_780207e8.prog s)
    -- `orchard::spec::extract_p`
    (hc_78020ca0 : CodeAt F_78020ca0.base F_78020ca0.prog s)
    -- `sinsemilla::CommitDomain::commit`
    (hc_78020d50 : CodeAt F_78020d50.base F_78020d50.prog s)
    -- `sinsemilla::CommitDomain::commit`
    (hc_78021238 : CodeAt F_78021238.base F_78021238.prog s)
    -- `keys::SpendAuthorizingKey::derive_unchecked`
    (hc_7802233c : CodeAt F_7802233c.base F_7802233c.prog s)
    -- `keys::SpendValidatingKey::from_bytes`
    (hc_78022514 : CodeAt F_78022514.base F_78022514.prog s)
    -- `keys::SpendValidatingKey::randomize`
    (hc_780227b4 : CodeAt F_780227b4.base F_780227b4.prog s)
    -- `keys::NullifierDerivingKey::from_bytes`
    (hc_78022848 : CodeAt F_78022848.base F_78022848.prog s)
    -- `keys::CommitIvkRandomness::from_bytes`
    (hc_78022a74 : CodeAt F_78022a74.base F_78022a74.prog s)
    -- `keys::FullViewingKey::rivk`
    (hc_78022ca0 : CodeAt F_78022ca0.base F_78022ca0.prog s)
    -- `<signing_key::SigningKey as convert::TryFrom>::try_from`
    (hc_78022f5c : CodeAt F_78022f5c.base F_78022f5c.prog s)
    -- `<keys::NullifierDerivingKey as convert::From>::from`
    (hc_780231e8 : CodeAt F_780231e8.base F_780231e8.prog s)
    -- `<keys::CommitIvkRandomness as convert::From>::from`
    (hc_78023230 : CodeAt F_78023230.base F_78023230.prog s)
    -- `<orchard::SpendAuth as private::Sealed>::basepoint`
    (hc_78023278 : CodeAt F_78023278.base F_78023278.prog s)
    -- `subtle::black_box`
    (hc_780232f4 : CodeAt F_780232f4.base F_780232f4.prog s)
    -- `prf_expand::PrfExpand::with`
    (hc_78023308 : CodeAt F_78023308.base F_78023308.prog s)
    -- `sinsemilla::extract_p_bottom`
    (hc_7802340c : CodeAt F_7802340c.base F_7802340c.prog s)
    -- `sinsemilla::lebs2ip_k`
    (hc_780234cc : CodeAt F_780234cc.base F_780234cc.prog s)
    -- `addition::IncompletePoint::bottom`
    (hc_78023544 : CodeAt F_78023544.base F_78023544.prog s)
    -- `sinsemilla::CommitDomain::blinding`
    (hc_78023594 : CodeAt F_78023594.base F_78023594.prog s)
    -- `sinsemilla::HashDomain::hash_to_point_inner::incomplete_add`
    (hc_780235e8 : CodeAt F_780235e8.base F_780235e8.prog s)
    -- `sinsemilla::HashDomain::hash_to_point_inner::pack`
    (hc_780237dc : CodeAt F_780237dc.base F_780237dc.prog s)
    -- `sinsemilla::HashDomain::hash_to_point_inner::unpack`
    (hc_78023864 : CodeAt F_78023864.base F_78023864.prog s)
    -- `<addition::IncompletePoint as convert::From>::from`
    (hc_780239bc : CodeAt F_780239bc.base F_780239bc.prog s)
    -- `<p128pow5t3::P128Pow5T3 as halo2_poseidon::Spec>::sbox`
    (hc_78023a18 : CodeAt F_78023a18.base F_78023a18.prog s)
    -- `<curves::Eq as subtle::ConditionallySelectable>::conditional_select`
    (hc_78023d7c : CodeAt F_78023d7c.base F_78023d7c.prog s)
    -- `<curves::Eq as group::Group>::is_identity`
    (hc_78023ec4 : CodeAt F_78023ec4.base F_78023ec4.prog s)
    -- `<curves::EqAffine as curves::CurveAffine>::coordinates`
    (hc_78023f64 : CodeAt F_78023f64.base F_78023f64.prog s)
    -- `<curves::Ep as group::Group>::double`
    (hc_7802413c : CodeAt F_7802413c.base F_7802413c.prog s)
    -- `<curves::IsoEp as group::Curve>::to_affine`
    (hc_78025164 : CodeAt F_78025164.base F_78025164.prog s)
    -- `<curves::IsoEp as group::GroupEncoding>::to_bytes`
    (hc_78025654 : CodeAt F_78025654.base F_78025654.prog s)
    -- `<curves::IsoEpAffine as prime::PrimeCurveAffine>::to_curve`
    (hc_78025854 : CodeAt F_78025854.base F_78025854.prog s)
    -- `<curves::EpAffine as group::GroupEncoding>::from_bytes`
    (hc_78025a1c : CodeAt F_78025a1c.base F_78025a1c.prog s)
    -- `<curves::EpAffine as curves::CurveAffine>::is_on_curve`
    (hc_78026258 : CodeAt F_78026258.base F_78026258.prog s)
    -- `<curves::EpAffine as curves::CurveAffine>::from_xy`
    (hc_78026878 : CodeAt F_78026878.base F_78026878.prog s)
    -- `<curves::Ep as group::GroupEncoding>::from_bytes`
    (hc_78026928 : CodeAt F_78026928.base F_78026928.prog s)
    -- `<curves::Ep as arith::Add>::add`
    (hc_78026b44 : CodeAt F_78026b44.base F_78026b44.prog s)
    -- `<curves::Ep as arith::Mul>::mul`
    (hc_7802827c : CodeAt F_7802827c.base F_7802827c.prog s)
    -- `fp::Fp::from_raw`
    (hc_78028298 : CodeAt F_78028298.base F_78028298.prog s)
    -- `fp::Fp::from_u512`
    (hc_78028718 : CodeAt F_78028718.base F_78028718.prog s)
    -- `<fp::Fp as subtle::ConstantTimeEq>::ct_eq`
    (hc_78028b34 : CodeAt F_78028b34.base F_78028b34.prog s)
    -- `<[u8; 32] as convert::From>::from`
    (hc_78028ce8 : CodeAt F_78028ce8.base F_78028ce8.prog s)
    -- `<fp::Fp as ff::Field>::invert`
    (hc_78028d04 : CodeAt F_78028d04.base F_78028d04.prog s)
    -- `<fp::Fp as ff::PrimeField>::to_repr`
    (hc_78029468 : CodeAt F_78029468.base F_78029468.prog s)
    -- `<fp::Fp as ff::PrimeField>::from_repr`
    (hc_780297c0 : CodeAt F_780297c0.base F_780297c0.prog s)
    -- `<fp::Fp as ff::PrimeField>::from_u128`
    (hc_78029ae8 : CodeAt F_78029ae8.base F_78029ae8.prog s)
    -- `<fp::Fp as ff::PrimeFieldBits>::to_le_bits`
    (hc_78029b18 : CodeAt F_78029b18.base F_78029b18.prog s)
    -- `<fp::Fp as fields::SqrtTableHelpers>::get_lower_32`
    (hc_78029b64 : CodeAt F_78029b64.base F_78029b64.prog s)
    -- `<fp::Fp as fields::SqrtTableHelpers>::pow_by_t_minus1_over2`
    (hc_78029d94 : CodeAt F_78029d94.base F_78029d94.prog s)
    -- `<fp::Fp as ff::FromUniformBytes>::from_uniform_bytes`
    (hc_7802e2b4 : CodeAt F_7802e2b4.base F_7802e2b4.prog s)
    -- `fq::Fq::from_u512`
    (hc_7802e5b4 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    -- `<fq::Fq as subtle::ConstantTimeEq>::ct_eq`
    (hc_7802e8ec : CodeAt F_7802e8ec.base F_7802e8ec.prog s)
    -- `<fq::Fq as ff::PrimeField>::to_repr`
    (hc_7802e9b8 : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    -- `<fq::Fq as ff::PrimeField>::from_repr`
    (hc_7802ed10 : CodeAt F_7802ed10.base F_7802ed10.prog s)
    -- `<fq::Fq as ff::FromUniformBytes>::from_uniform_bytes`
    (hc_7802f038 : CodeAt F_7802f038.base F_7802f038.prog s)
    -- `fields::SqrtTables::sqrt_common`
    (hc_7802f358 : CodeAt F_7802f358.base F_7802f358.prog s)
    -- `fields::SqrtTables::sqrt_alt`
    (hc_780315c0 : CodeAt F_780315c0.base F_780315c0.prog s)
    -- `zkvm::mul`
    (hc_78031be8 : CodeAt F_78031be8.base F_78031be8.prog s)
    -- `blake2b_simd::Params::to_state`
    (hc_78032c1c : CodeAt F_78032c1c.base F_78032c1c.prog s)
    -- `blake2b_simd::State::update`
    (hc_78032db4 : CodeAt F_78032db4.base F_78032db4.prog s)
    -- `blake2b_simd::State::finalize`
    (hc_78032fa4 : CodeAt F_78032fa4.base F_78032fa4.prog s)
    -- `blake2b_simd::portable::compress1_loop`
    (hc_78033260 : CodeAt F_78033260.base F_78033260.prog s)
    -- `<pallas::PallasPoint as utils::AffinePoint>::add_assign`
    (hc_78035f88 : CodeAt F_78035f88.base F_78035f88.prog s)
    -- `<pallas::PallasPoint as utils::AffinePoint>::complete_add_assign`
    (hc_78035fe0 : CodeAt F_78035fe0.base F_78035fe0.prog s)
    -- `<pallas::PallasPoint as utils::AffinePoint>::double`
    (hc_780360c8 : CodeAt F_780360c8.base F_780360c8.prog s)
    -- `<pallas::PallasPoint as utils::AffinePoint>::limbs_ref`
    (hc_780360e0 : CodeAt F_780360e0.base F_780360e0.prog s)
    -- `subtle::black_box`
    (hc_7803a0fc : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    -- `core::panicking::assert_failed`
    (hc_7803a110 : CodeAt F_7803a110.base F_7803a110.prog s)
    -- `core::panicking::assert_failed_inner`
    (hc_7803dd28 : CodeAt F_7803dd28.base F_7803dd28.prog s)
    -- `memcmp`
    (hc_7803f54c : CodeAt F_7803f54c.base F_7803f54c.prog s)
    -- `memset`
    (hc_7803f57c : CodeAt F_7803f57c.base F_7803f57c.prog s)
    -- `spin::Once::try_call_once_slow` — the one-time initialisation of `FP_TABLES`
    (hc_78032b38 : CodeAt F_78032b38.base F_78032b38.prog s)
    -- `SqrtTables::new` — builds `FP_TABLES`, `Fp`'s square-root tables
    (hc_78030a94 : CodeAt F_78030a94.base F_78030a94.prog s)
    -- `Vec::from_iter` — one of `SqrtTables::new`'s tables
    (hc_780326cc : CodeAt F_780326cc.base F_780326cc.prog s)
    -- `RawVecInner::reserve::do_reserve_and_handle` — growing a `SqrtTables` vector
    (hc_78032560 : CodeAt F_78032560.base F_78032560.prog s)
    -- `RawVecInner::finish_grow` — growing a `SqrtTables` vector
    (hc_78032614 : CodeAt F_78032614.base F_78032614.prog s)

    /- ### The rest of the entry state of `main` — proved from the ELF's entry (`Top/Elf`) -/
    -- The code map holds instructions only inside the text window: no jump can land on code the
    -- proofs have not accounted for.
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    -- The read-only segment (`.rodata`: constants, panic messages, `Location`s) holds the bytes
    -- of the ELF image.
    (hro : RoImage Ro.layout s)
    -- The heap invariant (`Run/Heap`): the TLSF allocator's control block at `0x78040620`
    -- represents a well-formed heap over the arena `[0x78048980, 0x1c00000000)`, each entry of
    -- `L` is null or the payload of its own used block, the allocation and panic hooks are
    -- unset, and the guest writes only inside its open ranges (`Run.ranges`) and live buffers.
    (hheap : Run.HeapAt L s)
    -- `x1` (the return-address register) holds `ra`, ...
    (hra : s.getReg .x1 = ra)
    -- ... and `ra` is 2-byte aligned (its low bit clear: a `jalr` back to it lands on `ra`).
    (hra1 : ra &&& ~~~1#64 = ra)
    -- `x2` (the stack pointer) holds `sp`, ...
    (hsp : s.getReg .x2 = sp)
    -- ... and `sp` is 16-byte aligned, below the stack top, with `0x3000` bytes of stack below
    -- it in low memory (under code, data and heap).
    (hstk : StackOk Ro.layout 0x3000 sp)
    -- The machine's private input is `I`.
    (hI : s.privateInput = I)
    -- `I` is shorter than `2^60` bytes (lengths fit a register without overflow).
    (hIl : I.length < 2 ^ 60)
    -- The hint-area pointer: the word at `0x78040618` holds `b`, ...
    (hB : Region 0x78040618#64 [b] s)
    -- ... which lies at or above the hint area's base `0x1c00000000`, ...
    (hb : 0x1c00000000 ≤ b.toNat)
    -- ... with 175 doublewords at `b` mapped and writable (the first record's buffer), ...
    (hokJ : RegionOk Ro.layout.textLo Ro.layout.textHi b 175)
    -- ... and the whole input, with its framing, fits below `0x2000000000` from `b`. This is
    -- the run's only precondition on the input itself (at the ELF's entry: `hIfit`,
    -- `I.length + 1416 ≤ 2^34`).
    (hbI : b.toNat + I.length + 1416 ≤ 0x2000000000)

    /- ### `FP_TABLES` -/
    -- `FP_TABLES` (`pasta_curves`' square-root tables, a `spin::Once` in `.bss`) is
    -- uninitialised at entry: ten zero words. The first point decompression builds it.
    (hT0 : Region 0x780488a8#64 [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] s)
    -- The allocator's contracts for building `FP_TABLES`. [Proved: `Run/SqContracts`.]
    -- `__rust_alloc(0x80, 8)` at `Vec::from_iter`'s first allocation.
    (hsq_alloc : SqAlloc G nb (Cases.Zip2005.Top.GuestAccepts I) s.code)
    -- `__rust_realloc` when `from_iter` grows a table (doubling). [Proved: `Run/SqContracts`.]
    (hsq_realloc_g : SqReallocG G nb (Cases.Zip2005.Top.GuestAccepts I) s.code)
    -- `__rust_alloc(1098, 1)` for the `inv` table. [Proved: `Run/SqContracts`.]
    (hsq_alloci : SqAllocInv G nb (Cases.Zip2005.Top.GuestAccepts I) s.code)
    -- `__rust_realloc` shrinking the last table to 516 doublewords. [Proved: `Run/SqContracts`.]
    (hsq_realloc : SqRealloc G nb (Cases.Zip2005.Top.GuestAccepts I) s.code)

    /- ### The panic and reject paths (`PanicPaths`) — the theorem's remaining assumptions

      Each says: a run that reaches this entry point (with a well-formed stack, the read-only
      segment intact and some valid heap) never accepts, i.e. it is `SafeN` for the conclusion.
      These (all but `hio`, which is proved) are the only hypotheses `Top/Guest.lean`'s
      `guest_run` leaves assumed (`PanicPaths`); every other hypothesis of this theorem is
      discharged there. -/
    -- `core::panicking::assert_failed` (`0x7803a110`), with one of the message/`Location`
    -- arguments the guest's call sites pass in `x15` (`Run.vals_a110`).
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `core::panicking::panic` (`0x7803de20`), with a message from `Run.vals_de20`.
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `panic_const_rem_by_zero` (`0x7803de78`): a remainder by zero, `Location` in
    -- `Run.vals_de78`.
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `core::panicking::panic_bounds_check` (`0x7803dcdc`): an index out of bounds,
    -- `Location` in `Run.vals_dcdc`.
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `core::panicking::panic_fmt` (`0x7803de40`): the general panic entry.
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `core::result::unwrap_failed` (`0x7803dc7c`): `.unwrap()` on an `Err`, with the
    -- message, error and `Location` among `Run.vals_dc7c_10/13/14`.
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `alloc::raw_vec::handle_error` (`0x7803cf14`): a `Vec` capacity overflow or failed
    -- growth.
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `alloc::alloc::handle_alloc_error` (`0x7803d1a8`): the allocator returned null.
    (hhandle_al : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `core::option::unwrap_failed` (`0x7803f364`): `.unwrap()` on a `None`, `Location` in
    -- `Run.vals_f364`.
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `core::panicking::assert_failed` (`0x78019da0`, the `orchard` instance).
    (hpaf_nf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78019da0#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `sp1_lib::halt_invalid_hint` (`0x78035e44`): the input stream is malformed (a record
    -- runs past the hint area); SP1 halts.
    (hhalt_hint : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035e44#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `empty_input_stream_halt` (`0x78035f14`): the input stream has no further record; SP1
    -- halts.
    (hhalt_empty : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x78035f14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `From<io::Error> for Box<bincode::ErrorKind>` (`0x78036184`), called on a read error:
    -- returns, keeping the heap. [Proved: `Run/Discharge`'s `hio_ok`, from `hhandle_al`.]
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `alloc::fmt::format::format_inner` (`0x7803d1cc`), called from `main` (return to
    -- `0x78019fa4`) to format an error message: it returns a 3-word `String` and keeps the
    -- heap. [Assumed: part of `PanicPaths`.]
    (hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78019fa4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78019fa4#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)

    /- ### The allocator and runtime contracts — proved

      Each is the contract of one runtime routine at the call sites that use it: it returns to
      the caller with the stated result, having changed only its own frame, the allocator's
      state and the arena. `Top/Guest.lean` derives every one of them from the code
      (`Run/Discharge`, `Run/ReallocContracts`, `Run/ReallocOr`, `Top/Assumptions`). -/
    -- `__rust_alloc(0x18, 8)` (`0x7801bcec`) from any call site: a 3-doubleword block, null or
    -- in the arena, added to the live list.
    (halloc : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = r' → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `__rust_alloc(0x80, 8)` when parsing the Merkle path (returning to `0x7801d114`).
    (halloc_mp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x80#64 →
      u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x80 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 16) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `RawVec<Fp>::reserve`'s slow path (`0x7801cac0`) when the Merkle path's `Vec` grows from
    -- `n` to `2n` elements, contents copied. [Proved: `reserve_mp_contract`.]
    (hreserve : ∀ (u : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word) (L' : List (Word × Nat)),
      u.pc = 0x7801cac0#64 → u.code = s.code → u.getReg .x1 = 0x7801d1e8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x100 sp' → u.getReg .x10 = hdr → u.getReg .x11 = BitVec.ofNat 64 n →
      Region hdr [BitVec.ofNat 64 n, ptr, BitVec.ofNat 64 n] u → RegionOk Ro.layout.roBase Ro.layout.textHi hdr 3 →
      Disjoint (sp' - 0x100#64) 32 hdr 3 → Disjoint 0x78040620#64 14780694332 hdr 3 → 4 ≤ n → n ≤ 16 →
      B.length = 4 * n → Region ptr B u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 32 * n ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, 4 * n) :: L') u →
      (∀ (t : MachineState) (ptr' : Word) (B' : List Word), t.pc = 0x7801d1e8#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region hdr [BitVec.ofNat 64 (2 * n), ptr', BitVec.ofNat 64 n] t → B'.length = 4 * n →
        Region ptr' (B ++ B') t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr' (8 * n) → 0x78048980 ≤ ptr'.toNat →
        ptr'.toNat + 64 * n ≤ 0x1c00000000 → Run.HeapAt ((ptr', 8 * n) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `__rust_dealloc(ptr, sz, 8)` (`0x7801bd08`) of a live block: it leaves the live list.
    (hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word) (k : Nat) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr →
      u.getReg .x11 = sz → u.getReg .x12 = 8#64 → 0x78048980 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `__rust_dealloc` of a hint-area pointer (a record `read_vec` returned, at or above
    -- `0x1c00000000`): the shim returns at once. [Proved: `Run/Discharge`'s `hdealloc_hint_ok`.]
    (hdealloc_hint : ∀ (u : MachineState) (sp' r ptr : Word) (L' : List (Word × Nat)), u.pc = 0x7801bd08#64 → u.code = s.code →
      u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → u.getReg .x10 = ptr → 0x1c00000000 ≤ ptr.toNat →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code → t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `__rust_dealloc` of Poseidon's 768-word round-constant table after `Nullifier::derive`'s
    -- hash (returning to `0x78020c64`).
    (hdealloc_nf : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 → u.getReg .x12 = 8#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `__rust_dealloc` of `commit_ivk`'s 65-word message-bit buffer (returning to
    -- `0x780215d8`), keeping `FP_TABLES` and its five heap tables intact.
    (hdealloc_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      0x78040620 ≤ iptr.toNat → 0x78040620 ≤ tg0.toNat → 0x78040620 ≤ tg1.toNat → 0x78040620 ≤ tg2.toNat →
      0x78040620 ≤ tg3.toNat → IV.length = 138 → G0.length = 1024 → G1.length = 1024 →
      G2.length = 1024 → G3.length = 516 → ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `__rust_dealloc` of `NoteCommitment::derive`'s 137-word message-bit buffer (returning to
    -- `0x780210f0`).
    (hdealloc_cm : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 → u.getReg .x2 = sp' →
      StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap → u.getReg .x12 = 1#64 →
      Region ptr C u → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `P128Pow5T3::constants()` (`0x78023cbc`): Poseidon's round constants allocated on the
    -- heap and its MDS matrices written out. [Proved: `constants_contract`.]
    (hconst : ∀ (u : MachineState) (sp' a0' : Word) (O1 O2 O3 : List Word) (L' : List (Word × Nat)),
      O1.length = 3 → O2.length = 36 → O3.length = 36 →
      u.pc = 0x78023cbc#64 → u.code = s.code → u.getReg .x1 = 0x7802084c#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x60 sp' → u.getReg .x10 = a0' →
      Region a0' O1 u → Region (a0' + 0x18#64) O2 u → Region (a0' + 0x138#64) O3 u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 75 → Disjoint (sp' - 0x60#64) 12 a0' 75 →
      RoImage Ro.layout u → Disjoint 0x78040620#64 14780694332 a0' 75 →
      Run.HeapAt L' u →
      (∀ t, t.pc = 0x7802084c#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x60#64, 12), (a0', 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        ∀ (ptr : Word) (MI : List Word), MI.length = 36 →
        Region a0' [64#64, ptr, 64#64] t → Region (a0' + 0x18#64) Poseidon.mdsWords t →
        Region (a0' + 0x138#64) MI t →
        Region ptr Poseidon.rcWords t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 768 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 768) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `Vec<bool>::from_iter` (`0x7801e110`) over `commit_ivk`'s message: a 510-bit buffer
    -- whose bits are `ivkBit` of `ak`, `nk`, keeping `FP_TABLES`. [Proved:
    -- `from_iter_ivk_contract`.]
    (hfrom_ivk : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word)
      (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (a0 a1 a2 a3 n0 n1 n2 n3 : Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterIvkW sp0 J0) u →
      Region (a1' + 0x58#64) [0#64] u →
      Region (sp0 - 0xaa0#64 + 0x9c8#64) (ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 12 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 12 →
      Disjoint a0' 3 a1' 12 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      StackOk Ro.layout 0xaa0 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a0' 3 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a1' 12 (sp0 - 0xaa0#64 + 0x9c8#64) 8 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 12 →
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 12 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 →
        (∀ o, o < 510 → byteAt Bv o = bw (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((ptr, 64) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u)
    -- `Vec<bool>::from_iter` (`0x7801dfb4`) over `NoteCommitment::derive`'s message: a
    -- 1090-bit buffer whose bits are `noteBit` of `g_d`, `pk_d`, `v`, `ρ`, `ψ`. [Proved:
    -- `from_iter_nc_contract`.]
    (hfrom_nc : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (g0 g1 g2 g3 p0 p1 p2 p3 v r0 r1 r2 r3 q0 q1 q2 q3 : Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801dfb4#64 → u.code = s.code → u.getReg .x1 = 0x78020dc4#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterW sp0 J0) u →
      Region (a1' + 0x88#64) [0#64] u →
      Region (sp0 - 0xb50#64 + 0xa80#64) ([g0, g1, g2, g3, p0, p1, p2, p3, v] ++
        reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 18 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 18 →
      Disjoint a0' 3 a1' 18 →
      StackOk Ro.layout 0xb50 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xb50#64 + 0xa80#64) 17 → Disjoint a0' 3 (sp0 - 0xb50#64 + 0xa80#64) 17 → Disjoint a1' 18 (sp0 - 0xb50#64 + 0xa80#64) 17 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 18 →
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 18 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 →
        (∀ o, o < 1090 → byteAt Bv o = bw (noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v
          (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 256) :: L') t → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) t) → SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) u) :
    /- ### The top-level theorem statement -/
    SafeN G nb (Cases.Zip2005.Top.GuestAccepts I) s := by
  exact main_spec (P := Cases.Zip2005.Top.GuestAccepts I) s ra sp b I hpc hc_78016938 hc_7801775c
    hc_7801806c hc_7801823c hc_780191c4 hc_780197cc hc_78019918 hc_78019a10 hc_78019b50 hc_78019bf0
    hc_78019cb8 hc_78019dd8 hc_78019f50 hc_78019ff4 hc_7801aed0 hc_7801b4d8 hc_7801beb0 hc_7801bf3c
    hc_7801bf4c hc_7801bf5c hc_7801cb44 hc_7801ce6c hc_7801ce90 hc_7801d074 hc_7801d098 hc_7801d2c8
    hc_7801d2ec hc_7801d360 hc_7801d3d4 hc_7801d51c hc_7801d92c hc_7801ddd8 hc_7801e26c hc_7801e704
    hc_7801ed68 hc_7801f120 hc_7801f5a4 hc_7801f780 hc_7801fb1c hc_7801fbcc hc_7802018c hc_780203dc
    hc_78020548 hc_780207e8 hc_78020ca0 hc_78020d50 hc_78021238 hc_7802233c hc_78022514 hc_780227b4
    hc_78022848 hc_78022a74 hc_78022ca0 hc_78022f5c hc_780231e8 hc_78023230 hc_78023278 hc_780232f4
    hc_78023308 hc_7802340c hc_780234cc hc_78023544 hc_78023594 hc_780235e8 hc_780237dc hc_78023864
    hc_780239bc hc_78023a18 hc_78023d7c hc_78023ec4 hc_78023f64 hc_7802413c hc_78025164 hc_78025654
    hc_78025854 hc_78025a1c hc_78026258 hc_78026878 hc_78026928 hc_78026b44 hc_7802827c hc_78028298
    hc_78028718 hc_78028b34 hc_78028ce8 hc_78028d04 hc_78029468 hc_780297c0 hc_78029ae8 hc_78029b18
    hc_78029b64 hc_78029d94 hc_7802e2b4 hc_7802e5b4 hc_7802e8ec hc_7802e9b8 hc_7802ed10 hc_7802f038
    hc_7802f358 hc_780315c0 hc_78031be8 hc_78032c1c hc_78032db4 hc_78032fa4 hc_78033260 hc_78035f88
    hc_78035fe0 hc_780360c8 hc_780360e0 hc_7803a0fc hc_7803a110 hc_7803dd28 hc_7803f54c hc_7803f57c hc_78032b38 hc_78030a94 hc_780326cc hc_78032560 hc_78032614
    hcw hro hheap hra hra1 hsp hstk hI hIl hB hb hokJ hbI 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 hT0 rfl hsq_alloc hsq_realloc_g hsq_alloci
    hsq_realloc hpaf hpp hprz hpb hpanic
    hunwrap hhandle_rv hhandle_al hunwrap_opt hpaf_nf hhalt_hint hhalt_empty hio hfmt halloc
    halloc_mp hreserve hdealloc hdealloc_hint hdealloc_nf hdealloc_ivk hdealloc_cm hconst hfrom_ivk
    hfrom_nc (fun t _ _ _ _ _ hacc => AsmVerif.RiscV.SafeN.of_true hacc t)

end Cases.Zip2005
