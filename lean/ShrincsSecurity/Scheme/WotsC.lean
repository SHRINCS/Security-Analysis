module

public import ShrincsSecurity.Scheme.Primitives
public import HashSig.SLHDSA.WotsInjectivity

/-!
# WOTS+C

`SHRINCS-Security-Analysis.pdf`, Section 2.4 (WOTS+C), Section 3.1 (proof of Lemma 3.1, Step 3),
and the constant-sum argument of Section 2.4 / Claim 4.10.

WOTS+C replaces the WOTS checksum by grinding: the signer searches the counters
`ctr = 0, 1, …, 2^c − 1` in increasing order for the first one such that the base-`w` digits of
`d = H_grind(PK.seed, ADRS_g, md, ctr)` sum to `Swn`, and fails (`⊥`) if there is none. The
verifier accepts any counter whose digits sum to `Swn`.

* Digits are FIPS 205's `base2b` of the `n/8`-byte encoding, most significant first; under the
  parameter validity they are VCVio's `SLHDSA.wotsMsgDigitsCore` at the stateless parameters
  (`digits_eq_wotsMsgDigitsCore`), whose injectivity VCVio proves (`digits_injective`).
* The chaining function is VCVio's FIPS 205 chain (`SLHDSA.chain`) at the `SF_WOTS_C_HASH`
  address of the chain: "the chaining function and key derivation are inherited from WOTS-TW
  without modification, up to the stateful address types" (Section 2.4).
* Key generation, signing and public-key recovery are parametric in the secret chain starts
  `sk : ℕ → Y`. The scheme derives them with `PRF` at `SF_WOTS_C_PRF` addresses
  (`prfSecret`); the idealized FXMSS game of Definition 4.16 samples them uniformly.
* `signWith` signs a given encoded digest and counter; this is what the S-TCR(Prop) oracle of the
  hop `F.2 → F.3` supplies.

Main results: `pkFromSig_sign` (the WOTS+C round trip of Lemma 3.1, Step 3), the grinding
specification `grind_eq_some_iff` / `grind_eq_none_iff` (bounded least counter), and the
constant-sum non-domination property `targetSum_incomparable` / `exists_digit_lt_of_ne`
(Section 2.4 and Claim 4.10: two distinct target-sum digests have incomparable digit vectors, so
some chain of the forgery lies strictly below the honest one).
-/

@[expose] public section

namespace ShrincsSecurity.Scheme.WotsC

open SLHDSA (Adrs Byte Bytes)

variable {P : Params} (pr : Primitives P)

/-! ## Digits and the target-sum predicate -/

/-- The `lsf` base-`w` digits `(a_0, …, a_{lsf−1})` of an `n`-bit value, most significant first. -/
def digits (y : pr.Y) : List ℕ := SLHDSA.base2b (pr.yToBytes y).toList P.lgw P.lsf

@[simp] theorem digits_length (y : pr.Y) : (digits pr y).length = P.lsf :=
  SLHDSA.base2b_length _ _ _

theorem digits_lt (y : pr.Y) : ∀ a ∈ digits pr y, a < P.w :=
  SLHDSA.base2b_lt _ _ _

/-- Under parameter validity the WOTS+C digits are VCVio's FIPS 205 message digits. -/
theorem digits_eq_wotsMsgDigitsCore (hP : P.Valid) (y : pr.Y) :
    digits pr y = SLHDSA.wotsMsgDigitsCore pr.toSLHDSA.toCorePrimitives y := by
  unfold digits SLHDSA.wotsMsgDigitsCore
  rw [Params.lsf_eq_len1 hP]
  rfl

/-- An `n`-bit value is determined by its `lsf` digits (Claim 4.10: "`d` is determined by its
`lsf` base-`w` digits"), given that the byte encoding is injective. -/
theorem digits_injective (hP : P.Valid) (hinj : Function.Injective pr.yToBytes) :
    Function.Injective (digits pr) := by
  have h := SLHDSA.wotsMsgDigitsCore_injective (core := pr.toSLHDSA.toCorePrimitives)
    hP.slValid ⟨hinj⟩
  intro x y hxy
  apply h
  rwa [← digits_eq_wotsMsgDigitsCore pr hP, ← digits_eq_wotsMsgDigitsCore pr hP]

/-- The digit `a_ch` (zero past the end). -/
def digit (y : pr.Y) (ch : ℕ) : ℕ := (digits pr y).getD ch 0

theorem digit_lt (y : pr.Y) (ch : ℕ) : digit pr y ch < P.w := by
  unfold digit
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge ch (digits pr y).length with h | h
  · rw [List.getElem?_eq_getElem h]
    exact digits_lt pr y _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]
    exact P.w_pos

/-- The digit sum `∑ a_i`. -/
def digitSum (y : pr.Y) : ℕ := (digits pr y).sum

/-- The WOTS+C target-sum predicate `Prop`: `∑_{i<lsf} a_i = Swn` (Section 2.4, Claim 4.3). -/
def TargetSum (y : pr.Y) : Prop := digitSum pr y = P.Swn

instance (y : pr.Y) : Decidable (TargetSum pr y) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## The constant-sum property -/

private theorem sum_le_of_forall₂ : ∀ {a b : List ℕ}, List.Forall₂ (· ≤ ·) a b → a.sum ≤ b.sum
  | [], [], .nil => le_rfl
  | _ :: _, _ :: _, .cons h hs => by
    simp only [List.sum_cons]
    exact Nat.add_le_add h (sum_le_of_forall₂ hs)

/-- Two digit lists with equal sums, one pointwise below the other, are equal. -/
theorem eq_of_forall₂_le_of_sum_eq :
    ∀ {a b : List ℕ}, List.Forall₂ (· ≤ ·) a b → a.sum = b.sum → a = b
  | [], [], .nil, _ => rfl
  | x :: a, y :: b, .cons hxy hab, hs => by
    have hle := sum_le_of_forall₂ hab
    simp only [List.sum_cons] at hs
    have hxy' : x = y := by omega
    subst hxy'
    rw [eq_of_forall₂_le_of_sum_eq hab (by omega)]

/-- **Constant-sum non-domination** (Section 2.4): if two encoded digests both meet the target
sum and have different digit vectors, then neither digit vector is pointwise below the other. -/
theorem targetSum_incomparable {d d' : pr.Y} (hd : TargetSum pr d) (hd' : TargetSum pr d')
    (hne : digits pr d ≠ digits pr d') :
    ¬ List.Forall₂ (· ≤ ·) (digits pr d) (digits pr d') ∧
      ¬ List.Forall₂ (· ≤ ·) (digits pr d') (digits pr d) := by
  have hs : (digits pr d).sum = (digits pr d').sum := hd.trans hd'.symm
  exact ⟨fun h => hne (eq_of_forall₂_le_of_sum_eq h hs),
    fun h => hne (eq_of_forall₂_le_of_sum_eq h hs.symm).symm⟩

/-- The index-wise form used in Claim 4.10: for two target-sum digests with different digit
vectors, some chain `ch < lsf` has `a_ch < a'_ch`. With `d` the forgery's encoded digest and
`d'` the honest one, the forgery's chain `ch` starts strictly below the revealed chain value. -/
theorem exists_digit_lt {d d' : pr.Y} (hd : TargetSum pr d) (hd' : TargetSum pr d')
    (hne : digits pr d ≠ digits pr d') : ∃ ch < P.lsf, digit pr d ch < digit pr d' ch := by
  by_contra hnot
  simp only [not_exists, not_and, not_lt] at hnot
  refine (targetSum_incomparable pr hd hd' hne).2 ?_
  refine List.forall₂_of_length_eq_of_get (by simp) fun i hi hi' => ?_
  have h := hnot i (by simpa using hi)
  simp only [digit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hi', Option.getD_some] at h
  simpa using h

/-- `exists_digit_lt` for distinct encoded digests, using that digits determine the value. -/
theorem exists_digit_lt_of_ne (hP : P.Valid) (hinj : Function.Injective pr.yToBytes)
    {d d' : pr.Y} (hd : TargetSum pr d) (hd' : TargetSum pr d') (hne : d ≠ d') :
    ∃ ch < P.lsf, digit pr d ch < digit pr d' ch :=
  exists_digit_lt pr hd hd' fun h => hne (digits_injective pr hP hinj h)

/-! ## Grinding -/

/-- The encoded digest `H_grind(PK.seed, ADRS_g[0:10], md, ctr)` at the grinding address of the
WOTS+C instance `id`. -/
def encode (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) (ctr : Fin (2 ^ P.c)) : pr.Y :=
  pr.Hgrind pk (SfAdrs.grindAdrs id).toAdrs md ctr

/-- **Grinding step** `(d, ctr) ← grind(m, PK.seed, ADRS_g)` (Section 2.4): the least counter
below `2^c` whose encoded digest meets the target sum, or `⊥`. -/
def grind (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) : Option (pr.Y × Fin (2 ^ P.c)) :=
  if h : ∃ ctr, TargetSum pr (encode pr pk id md ctr) then
    some (encode pr pk id md (Fin.find _ h), Fin.find _ h)
  else none

/-- Grinding returns the encoded digest at the **least** valid counter (the iteration order is
normative, Section 2.4). -/
theorem grind_eq_some_iff {pk : pr.PkSeed} {id : LeafId} {md : pr.Digest} {d : pr.Y}
    {ctr : Fin (2 ^ P.c)} :
    grind pr pk id md = some (d, ctr) ↔
      d = encode pr pk id md ctr ∧ TargetSum pr d ∧
        ∀ ctr' < ctr, ¬ TargetSum pr (encode pr pk id md ctr') := by
  unfold grind
  split_ifs with h
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, Fin.find_spec h, fun _ h' => Fin.find_min h h'⟩
    · rintro ⟨rfl, hT, hmin⟩
      have hf : Fin.find _ h = ctr := (Fin.find_eq_iff h).2 ⟨hT, hmin⟩
      exact ⟨by rw [hf], hf⟩
  · simp only [false_iff, not_and]
    rintro rfl hT
    exact absurd ⟨ctr, hT⟩ h

/-- Grinding fails exactly when no counter below `2^c` meets the target sum. -/
theorem grind_eq_none_iff {pk : pr.PkSeed} {id : LeafId} {md : pr.Digest} :
    grind pr pk id md = none ↔ ∀ ctr, ¬ TargetSum pr (encode pr pk id md ctr) := by
  unfold grind
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    exact h
  · simpa using h

/-! ## Chains -/

/-- The chaining function `c_{j,k}(x, ch, PK.seed, ADRS)` of the WOTS+C instance at `id`
(Section 2.3/2.4): VCVio's FIPS 205 chain at the `SF_WOTS_C_HASH` address of chain `ch`. -/
def chain (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j k : ℕ) : pr.Y :=
  SLHDSA.chain pr.toSLHDSA pk (SfAdrs.chainAdrs id ch 0).toAdrs x j k

@[simp] theorem chain_zero (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j : ℕ) :
    chain pr pk id ch x j 0 = x := rfl

/-- One chain step evaluates `F` at hash address `j + k` (Section 2.3). -/
theorem chain_succ (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j k : ℕ) :
    chain pr pk id ch x j (k + 1) =
      pr.F pk (SfAdrs.chainAdrs id ch (j + k)).toAdrs (chain pr pk id ch x j k) :=
  SLHDSA.chain_succ _ _ _ _ _ _

/-- Chain composition `c_{j+a, b} ∘ c_{j, a} = c_{j, a+b}` (Lemma 3.1, Step 3). -/
theorem chain_compose (pk : pr.PkSeed) (id : LeafId) (ch : ℕ) (x : pr.Y) (j a b : ℕ) :
    chain pr pk id ch (chain pr pk id ch x j a) (j + a) b = chain pr pk id ch x j (a + b) :=
  SLHDSA.chain_compose _ _ _ _ _ _ _

/-! ## Key generation, signing, public-key recovery -/

/-- A WOTS+C signature `(ctr, σ_0, …, σ_{lsf−1})`. -/
structure Sig (pr : Primitives P) where
  /-- The grinding counter. -/
  ctr : Fin (2 ^ P.c)
  /-- The `lsf` chain values. -/
  chains : Vector pr.Y P.lsf

/-- The secret chain starts derived by `PRF(PK.seed, SK.seed, ADRS_i)` at the `SF_WOTS_C_PRF`
addresses of the instance `id`, carrying the structure bytes `tag` (Section 2.4). -/
def prfSecret (pk : pr.PkSeed) (skSeed : pr.SkSeed) (tag : ℕ) (id : LeafId) (ch : ℕ) : pr.Y :=
  pr.PRF pk skSeed (SfAdrs.prfAdrs tag id ch).toAdrs

/-- The uncompressed public key `pk_i = c_{0, w−1}(sk_i)`. -/
def pkTops (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) : Vector pr.Y P.lsf :=
  Vector.ofFn fun ch => chain pr pk id ch.val (sk ch.val) 0 (P.w - 1)

/-- **Key generation** `WOTS+C.kg(...).pk = Th_lsf(PK.seed, ADRS_pk, pk_0 ‖ … ‖ pk_{lsf−1})`. -/
def pkGen (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) : pr.Y :=
  pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs (pkTops pr pk id sk)

/-- The signature chains `σ_i = c_{0, a_i}(sk_i)` for the digits of `d`. -/
def signChains (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) (d : pr.Y) : Vector pr.Y P.lsf :=
  Vector.ofFn fun ch => chain pr pk id ch.val (sk ch.val) 0 (digit pr d ch.val)

/-- Sign a given encoded digest `d` with counter `ctr`. -/
def signWith (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) (d : pr.Y) (ctr : Fin (2 ^ P.c)) :
    Sig pr :=
  ⟨ctr, signChains pr pk id sk d⟩

/-- **Signature algorithm** `σ ← WOTS+C.sign(md, SK)` (Section 2.4): grind, then reveal the chain
values at the digits; `⊥` if grinding fails. -/
def sign (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) (md : pr.Digest) : Option (Sig pr) :=
  (grind pr pk id md).map fun dc => signWith pr pk id sk dc.1 dc.2

/-- The chain ends recomputed from a signature for encoded digest `d`:
`pk'_i = c_{a_i, w−1−a_i}(σ_i)`. -/
def topsFromSig (pk : pr.PkSeed) (id : LeafId) (d : pr.Y) (σ : Sig pr) : Vector pr.Y P.lsf :=
  Vector.ofFn fun ch =>
    chain pr pk id ch.val σ.chains[ch.val] (digit pr d ch.val) (P.w - 1 - digit pr d ch.val)

/-- **Public-key recovery** `WOTS+C.pkFromSig(md, σ, PK.seed, ADRS)` (Section 2.4): recompute the
encoded digest at the signature's counter, return `⊥` unless it meets the target sum, otherwise
complete the chains and compress. Minimality of the counter is not checked. -/
def pkFromSig (pk : pr.PkSeed) (id : LeafId) (md : pr.Digest) (σ : Sig pr) : Option pr.Y :=
  let d := encode pr pk id md σ.ctr
  if TargetSum pr d then some (pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs (topsFromSig pr pk id d σ))
  else none

theorem topsFromSig_signWith (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) (d : pr.Y)
    (ctr : Fin (2 ^ P.c)) :
    topsFromSig pr pk id d (signWith pr pk id sk d ctr) = pkTops pr pk id sk := by
  apply Vector.ext
  intro i hi
  simp only [topsFromSig, signWith, signChains, pkTops, Vector.getElem_ofFn]
  have hc := chain_compose pr pk id i (sk i) 0 (digit pr d i) (P.w - 1 - digit pr d i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (digit_lt pr d i))]

/-- Recovery from a signature of a target-sum digest returns the public key. -/
theorem pkFromSig_signWith (pk : pr.PkSeed) (id : LeafId) (sk : ℕ → pr.Y) (md : pr.Digest)
    (ctr : Fin (2 ^ P.c)) (hT : TargetSum pr (encode pr pk id md ctr)) :
    pkFromSig pr pk id md (signWith pr pk id sk (encode pr pk id md ctr) ctr) =
      some (pkGen pr pk id sk) := by
  have h := topsFromSig_signWith pr pk id sk (encode pr pk id md ctr) ctr
  unfold signWith at h
  simp only [pkFromSig, signWith, hT, ↓reduceIte, h]
  rfl

/-- **WOTS+C round trip** (Lemma 3.1, Step 3): a non-`⊥` honest signature recovers the public
key. -/
theorem pkFromSig_sign {pk : pr.PkSeed} {id : LeafId} {sk : ℕ → pr.Y} {md : pr.Digest}
    {σ : Sig pr} (h : sign pr pk id sk md = some σ) :
    pkFromSig pr pk id md σ = some (pkGen pr pk id sk) := by
  unfold sign at h
  obtain ⟨⟨d, ctr⟩, hg, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨rfl, hT, -⟩ := (grind_eq_some_iff pr).1 hg
  exact pkFromSig_signWith pr pk id sk md ctr hT

/-- WOTS+C signing fails exactly when grinding fails (Lemma 3.1 (i)). -/
theorem sign_eq_none_iff {pk : pr.PkSeed} {id : LeafId} {sk : ℕ → pr.Y} {md : pr.Digest} :
    sign pr pk id sk md = none ↔ grind pr pk id md = none := by
  simp [sign]

/-- The honest signature of a non-`⊥` signing call: the least valid counter and the chain values
at the digits of the encoded digest, which meets the target sum. -/
theorem sign_eq_some_iff {pk : pr.PkSeed} {id : LeafId} {sk : ℕ → pr.Y} {md : pr.Digest}
    {σ : Sig pr} :
    sign pr pk id sk md = some σ ↔
      grind pr pk id md = some (encode pr pk id md σ.ctr, σ.ctr) ∧
        σ = signWith pr pk id sk (encode pr pk id md σ.ctr) σ.ctr := by
  constructor
  · intro h
    unfold sign at h
    obtain ⟨⟨d, ctr⟩, hg, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨rfl, -, -⟩ := (grind_eq_some_iff pr).1 hg
    exact ⟨hg, rfl⟩
  · rintro ⟨hg, hσ⟩
    simp only [sign, hg, Option.map_some]
    rw [hσ.symm]

/-- **Inversion of recovery**: the verifier accepts only counters whose encoded digest meets the
target sum (Claim 4.10), and then returns the compression of the completed chains. -/
theorem pkFromSig_eq_some_iff {pk : pr.PkSeed} {id : LeafId} {md : pr.Digest} {σ : Sig pr}
    {r : pr.Y} :
    pkFromSig pr pk id md σ = some r ↔
      TargetSum pr (encode pr pk id md σ.ctr) ∧
        r = pr.ThLsf pk (SfAdrs.pkAdrs id).toAdrs
          (topsFromSig pr pk id (encode pr pk id md σ.ctr) σ) := by
  unfold pkFromSig
  simp only
  split_ifs with h
  · simp [h, eq_comm]
  · simp [h]

end ShrincsSecurity.Scheme.WotsC
