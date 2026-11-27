module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Tactic.Ring

/-!
# Evidence: small finite facts about `SHRINCS-Security-Analysis.pdf`

* **Definition 4.8** (p. 36–37, S-TCR(Prop)): the oracle step "Find the smallest `i ∈ ℕ` with
  `Prop(Th(P, T, m‖i)) = 1`" has no value when no counter satisfies `Prop`
  (`stcr_no_valid_counter`).
* **Section 2.2 / Algorithm 4–5** (pp. 6, 8, 52–53): the leaf identifier
  `idx = toByte(z*, 1) ‖ toByte(i*, 8)`. With the total `toByte` of FIPS 205 (Algorithm 3, the low
  `y` bytes of `x`, big-endian) it is injective on `z* < 256`, `i* < 2^64` (`idx_injOn`) and
  collides outside that range (`idx_collide_height`, `idx_collide_index`).
* **Claim 4.10** (p. 61): "`d` is determined by its `l_sf` base-`w` digits": `d ∈ {0,1}^n` with
  `n = 128 = 32 · 4 = l_sf · log₂ w` (Table 1, p. 6), so the `32` base-`16` digits determine `d`
  (`claim410_digits_determine`).
-/

@[expose] public section

namespace ShrincsSecurity.Evidence.MainPaper

/-! ## Base-`b` digits determine a number below `b ^ n` -/

/-- `x mod b^k` is determined by the first `k` base-`b` digits. -/
theorem mod_pow_eq_of_digits_eq {b x x' : ℕ} :
    ∀ k : ℕ, (∀ i < k, x / b ^ i % b = x' / b ^ i % b) → x % b ^ k = x' % b ^ k
  | 0, _ => by simp [Nat.mod_one]
  | k + 1, h => by
    rw [Nat.mod_pow_succ, Nat.mod_pow_succ,
      mod_pow_eq_of_digits_eq k fun i hi => h i (by omega), h k (by omega)]

/-- Two numbers below `b ^ n` with the same `n` base-`b` digits are equal. -/
theorem eq_of_digits_eq {b n x x' : ℕ} (hx : x < b ^ n) (hx' : x' < b ^ n)
    (h : ∀ i < n, x / b ^ i % b = x' / b ^ i % b) : x = x' := by
  have := mod_pow_eq_of_digits_eq n h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at this

/-! ## Definition 4.8: the least valid counter need not exist -/

/-- A toy grinding function: `l = 2` base-`2` digits, digest `0b00` on even counters and `0b11` on
odd counters (any `Th` whose values avoid the predicate behaves the same way). -/
def thToy (i : ℕ) : ℕ := if i % 2 = 0 then 0 else 3

/-- The target-sum predicate with `l = 2` base-`2` digits and target `S = 1`. -/
def propSum (d : ℕ) : Bool := decide (d / 2 % 2 + d % 2 = 1)

/-- No counter `i ∈ ℕ` satisfies `Prop(Th(P, T, m‖i)) = 1`: the "smallest such `i`" of
Definition 4.8 is undefined for this `(Th, Prop)`. -/
theorem stcr_no_valid_counter : ¬ ∃ i : ℕ, propSum (thToy i) = true := by
  rintro ⟨i, h⟩
  unfold thToy at h
  split at h <;> revert h <;> decide

/-! ## The leaf identifier `idx` -/

/-- `toByte(x, y)`: the `y`-byte big-endian encoding of `x`, total as in FIPS 205 Algorithm 3
(the low `y` bytes of `x`). -/
def toByte (x y : ℕ) : List ℕ := List.ofFn fun j : Fin y => x / 256 ^ (y - 1 - j.val) % 256

/-- `idx = toByte(z*, 1) ‖ toByte(i*, 8)`. -/
def idx (z i : ℕ) : List ℕ := toByte z 1 ++ toByte i 8

theorem length_toByte (x y : ℕ) : (toByte x y).length = y := by simp [toByte]

/-- `toByte(·, y)` is injective below `256 ^ y`. -/
theorem toByte_injOn {x x' y : ℕ} (hx : x < 256 ^ y) (hx' : x' < 256 ^ y)
    (h : toByte x y = toByte x' y) : x = x' := by
  have hf := List.ofFn_inj.mp h
  refine eq_of_digits_eq hx hx' fun i hi => ?_
  have := congrFun hf ⟨y - 1 - i, by omega⟩
  simp only [show y - 1 - (y - 1 - i) = i by omega] at this
  exact this

/-- Inside the stated ranges (`z* ≤ h_sf = 255`, `i* < 2^64`), `idx` is injective. -/
theorem idx_injOn {z z' i i' : ℕ} (hz : z < 256) (hz' : z' < 256) (hi : i < 2 ^ 64)
    (hi' : i' < 2 ^ 64) (h : idx z i = idx z' i') : z = z' ∧ i = i' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [length_toByte])
  exact ⟨toByte_injOn (by simpa using hz) (by simpa using hz') h1,
    toByte_injOn (by norm_num at hi ⊢; omega) (by norm_num at hi' ⊢; omega) h2⟩

/-- Outside the range: height `256` collides with height `0`. -/
theorem idx_collide_height : idx 256 0 = idx 0 0 := by decide

/-- Outside the range: index `2^64` collides with index `0`. -/
theorem idx_collide_index : idx 0 (2 ^ 64) = idx 0 0 := by decide

/-! ## Claim 4.10: the digits of the encoded digest -/

/-- Table 1 (p. 6): `n = 128`, `w = 16`, `l_sf = 32`, so `n = l_sf · log₂ w` and
`2^n = w^{l_sf}`. -/
theorem n_eq_lsf_mul_log_w : (128 : ℕ) = 32 * Nat.log 2 16 ∧ (2 : ℕ) ^ 128 = 16 ^ 32 := by
  refine ⟨?_, by norm_num⟩
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.log_pow (by norm_num)]

/-- **Claim 4.10**, "`d` is determined by its `l_sf` base-`w` digits": two `n`-bit encoded digests
with the same `32` base-`16` digits are equal. -/
theorem claim410_digits_determine {d d' : ℕ} (hd : d < 2 ^ 128) (hd' : d' < 2 ^ 128)
    (h : ∀ i < 32, d / 16 ^ i % 16 = d' / 16 ^ i % 16) : d = d' :=
  eq_of_digits_eq (b := 16) (n := 32) (by rw [← n_eq_lsf_mul_log_w.2]; exact hd)
    (by rw [← n_eq_lsf_mul_log_w.2]; exact hd') h

end ShrincsSecurity.Evidence.MainPaper

end
