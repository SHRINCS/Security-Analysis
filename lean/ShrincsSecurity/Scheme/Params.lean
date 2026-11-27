module

public import HashSig.SLHDSA.Params

/-!
# SHRINCS parameters (Table 1)

`SHRINCS-Security-Analysis.pdf`, Section 2.1 (Table 1, Remark 2.2), Section 2.3 (WOTS-TW
lengths), Section 2.4 (WOTS+C lengths).

Following Table 1 and Remark 2.2, the length parameters `n` and `c` are measured in **bits**. The
stateless path is SLH-DSA with a non-standard parameter set; `Params.slParams` is that parameter
set in the byte convention of FIPS 205 (and of VCVio's `SLHDSA.Params`), so that the stateless path
is literally VCVio's SLH-DSA development at these parameters.

The derived quantities are the paper's formulas:

* `w = 2^lgw`, `lsf = n / log₂ w`, `Swn = ⌈lsf (w − 1) / 2⌉` (Section 2.4);
* `l1 = n / log₂ w`, `l2 = ⌊log_w (l1 (w − 1))⌋ + 1`, `lsl = l1 + l2` (Section 2.3);
* `hsl = d · h'`, `t = 2^a`, and the digest length `m` (in bits) consumed by the stateless path.
-/

@[expose] public section

namespace ShrincsSecurity.Scheme

/-- **Table 1** (Parameters of SHRINCS). The primary parameters; all others are derived.
`n` and `c` are bit lengths (Remark 2.2); `lgw = log₂ w`. -/
structure Params where
  /-- Security parameter `n`: hash output length in bits. -/
  n : ℕ
  /-- `log₂ w`, the number of bits per Winternitz digit. -/
  lgw : ℕ
  /-- WOTS+C grinding-counter length `c` in bits (at most `2^c` attempts). -/
  c : ℕ
  /-- Number of hypertree layers `d` (stateless path). -/
  d : ℕ
  /-- Height `h'` of each XMSS tree of the hypertree. -/
  hp : ℕ
  /-- Number of FORS trees `k`. -/
  k : ℕ
  /-- Height `a` of each FORS tree. -/
  a : ℕ
  /-- Height `hsf` of the imaginary complete binary tree hosting the FXMSS tree. -/
  hsf : ℕ
deriving Repr, DecidableEq

namespace Params

variable (P : Params)

/-- The Winternitz parameter `w = 2^lgw`. -/
def w : ℕ := 2 ^ P.lgw

/-- Number of WOTS+C chains `lsf = n / log₂ w` (Section 2.4). -/
def lsf : ℕ := P.n / P.lgw

/-- The WOTS+C target chain sum `Swn = ⌈lsf (w − 1) / 2⌉` (Section 2.4). -/
def Swn : ℕ := (P.lsf * (P.w - 1) + 1) / 2

/-- Number of WOTS-TW message chains `l1 = n / log₂ w` (Section 2.3). -/
def l1 : ℕ := P.n / P.lgw

/-- Number of WOTS-TW checksum chains `l2 = ⌊log₂(l1 (w − 1)) / log₂ w⌋ + 1` (Section 2.3). -/
def l2 : ℕ := Nat.log P.w (P.l1 * (P.w - 1)) + 1

/-- Number of WOTS-TW chains `lsl = l1 + l2` (Section 2.3). -/
def lsl : ℕ := P.l1 + P.l2

/-- Total hypertree height `hsl = d · h'`. -/
def hsl : ℕ := P.d * P.hp

/-- Leaves per FORS tree `t = 2^a`. -/
def t : ℕ := 2 ^ P.a

/-- The SLH-DSA parameter set of the stateless path, in the byte convention of FIPS 205. -/
def slParams : SLHDSA.Params where
  n := P.n / 8
  h := P.hsl
  d := P.d
  hp := P.hp
  a := P.a
  k := P.k
  lgw := P.lgw

/-- Digest bits consumed by the stateless path, `m = 8⌈ka/8⌉ + 8⌈(hsl − h')/8⌉ + 8⌈h'/8⌉`, i.e.
eight times the FIPS 205 digest length of `slParams` (Table 1, Section 2.7). -/
def m : ℕ := 8 * P.slParams.m

/-- Well-formedness of the SHRINCS parameters. -/
structure Valid : Prop where
  n_pos : 0 < P.n
  /-- `n` is a whole number of bytes. -/
  n_bytes : 8 ∣ P.n
  lgw_pos : 0 < P.lgw
  /-- Digits consume exactly the `n` bits of a node. -/
  lgw_dvd : P.lgw ∣ P.n
  /-- The counter is a whole number of bytes. -/
  c_bytes : 8 ∣ P.c
  d_pos : 0 < P.d
  hp_pos : 0 < P.hp
  a_pos : 0 < P.a
  k_pos : 0 < P.k
  hsf_pos : 0 < P.hsf
  /-- The node height of a stateful address is a single byte (Fig. 2). -/
  hsf_le : P.hsf ≤ 255

variable {P}

theorem Valid.slValid (hP : P.Valid) : P.slParams.Valid where
  n_pos := by
    have := hP.n_pos; have := hP.n_bytes
    simp only [slParams]; omega
  d_pos := hP.d_pos
  hp_pos := hP.hp_pos
  a_pos := hP.a_pos
  k_pos := hP.k_pos
  lgw_pos := hP.lgw_pos
  wots_input_aligned := by
    simp only [slParams]
    rw [Nat.mul_div_cancel' hP.n_bytes]
    exact hP.lgw_dvd
  h_eq_layers := rfl

/-- The Winternitz parameter is that of the stateless SLH-DSA parameter set. -/
theorem w_eq_slParams_w : P.w = P.slParams.w := rfl

theorem w_pos : 0 < P.w := Nat.two_pow_pos _

theorem one_lt_w (hP : P.Valid) : 1 < P.w := Nat.one_lt_two_pow (Nat.ne_of_gt hP.lgw_pos)

/-- `l1 = lsf`: WOTS-TW and WOTS+C split an `n`-bit value into the same number of digits. -/
theorem l1_eq_lsf : P.l1 = P.lsf := rfl

/-- `lsf` is FIPS 205's `len1` of the stateless parameter set. -/
theorem lsf_eq_len1 (hP : P.Valid) : P.lsf = P.slParams.len1 := by
  have h := hP.slValid.len1_mul_lgw
  have h8 : 8 * P.slParams.n = P.n := Nat.mul_div_cancel' hP.n_bytes
  rw [h8] at h
  exact Nat.div_eq_of_eq_mul_left hP.lgw_pos h.symm

/-- `lsl` is FIPS 205's `len` of the stateless parameter set. -/
theorem lsl_eq_len (hP : P.Valid) : P.lsl = P.slParams.len := by
  have h : P.l1 = P.slParams.len1 := lsf_eq_len1 hP
  show P.l1 + (Nat.log P.w (P.l1 * (P.w - 1)) + 1) =
    P.slParams.len1 + (Nat.log P.slParams.w (P.slParams.len1 * (P.slParams.w - 1)) + 1)
  rw [h]
  rfl

/-- The target sum does not exceed the maximal digit sum. -/
theorem Swn_le : P.Swn ≤ P.lsf * (P.w - 1) := by
  unfold Swn; omega

end Params

/-- SHRINCS parameters paired with a proof of their validity. -/
structure ValidatedParams where
  params : Params
  valid : params.Valid

/-- The validated SLH-DSA parameter set of the stateless path. -/
@[reducible] def ValidatedParams.sl (vp : ValidatedParams) : SLHDSA.ValidatedParams :=
  ⟨vp.params.slParams, vp.valid.slValid⟩

/-- **Table 1**: the single SHRINCS parameter set (`n = 128`, `w = 16`, `c = 16`, `d = 5`,
`h' = 9`, `k = 10`, `a = 13`, `hsf = 255`). -/
def shrincs : Params where
  n := 128
  lgw := 4
  c := 16
  d := 5
  hp := 9
  k := 10
  a := 13
  hsf := 255

theorem shrincs_valid : shrincs.Valid where
  n_pos := by decide
  n_bytes := by decide
  lgw_pos := by decide
  lgw_dvd := by decide
  c_bytes := by decide
  d_pos := by decide
  hp_pos := by decide
  a_pos := by decide
  k_pos := by decide
  hsf_pos := by decide
  hsf_le := by decide

/-- The SHRINCS parameter set, validated. -/
def shrincsValidated : ValidatedParams := ⟨shrincs, shrincs_valid⟩

/-- **Table 1**, derived rows: `w = 16`, `lsf = 32`, `Swn = 240`, `l1 = 32`, `l2 = 3`, `lsl = 35`,
`hsl = 45`, `t = 2^13` and `m = 192` bits. -/
theorem shrincs_table1 :
    shrincs.w = 16 ∧ shrincs.lsf = 32 ∧ shrincs.Swn = 240 ∧ shrincs.l1 = 32 ∧
      shrincs.l2 = 3 ∧ shrincs.lsl = 35 ∧ shrincs.hsl = 45 ∧ shrincs.t = 2 ^ 13 ∧
      shrincs.m = 192 := by
  decide

/-- The stateless path is SLH-DSA with `n = 16` bytes, `h = 45`, `d = 5`, `h' = 9`, `a = 13`,
`k = 10`, `w = 16` (Section 2.7); its digest is `24 = 17 + 5 + 2` bytes and its signature
`5776` bytes. -/
theorem shrincs_slParams :
    shrincs.slParams = { n := 16, h := 45, d := 5, hp := 9, a := 13, k := 10, lgw := 4 } ∧
      shrincs.slParams.digestBytes = 17 ∧ shrincs.slParams.treeIdxBytes = 5 ∧
      shrincs.slParams.leafIdxBytes = 2 ∧ shrincs.slParams.m = 24 ∧
      shrincs.slParams.len = 35 ∧ shrincs.slParams.signatureBytes = 5776 := by
  decide

end ShrincsSecurity.Scheme
