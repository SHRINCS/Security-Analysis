module

public import ShrincsSecurity.Concrete.Quantum.Generic
public import ShrincsSecurity.Concrete.Conventions

/-!
# Rational enclosures of the quantum bounds

Every quantum bound of Section 6 at the parameters of Table 1 has the shape
`r + g Γ + Σᵢ cᵢ √nᵢ` with `r, g, cᵢ` rational, `g, cᵢ ≥ 0` and `nᵢ` natural (`Γ` from
Section 6.3). `Enc` records `(r, g, [(cᵢ, nᵢ)])`; `Enc.val` is the real number. The kernel encloses
it between the rationals `Enc.lo` and `Enc.hi`:

* `Γ` between `gamLo = 500371773772050553103/2^199` (below `gammaLoQ 12 ≤ Γ`) and
  `gamHi = 7822208915061017503/2^193` (`Gam_le_Q`);
* `√n` between `s/2^32` and `(s+1)/2^32`, where `s = isqrtN (n · 2^64)` is computed by Newton's
  method; the kernel checks `s² ≤ n · 2^64 ≤ (s+1)²` (`sqrtOk`), so the computation of `s` needs no
  proof.

`Enc.lt_one`, `Enc.one_le` and `Enc.logb_bracket` turn one `decide +kernel` evaluation into
`val < 1`, `1 ≤ val` and a bracket of `log₂ val`.
-/

@[expose] public section

namespace ShrincsSecurity.Concrete.Quantum

open ShrincsSecurity.Concrete

/-! ## Integer square roots -/

/-- Newton's iteration for `⌊√n⌋` from `x`, with fuel. -/
def isqrtAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | k + 1, n, x =>
    let y := (x + n / x) / 2
    if y < x then isqrtAux k n y else x

/-- An integer square root candidate; only `sqrtOk` is trusted. -/
def isqrtN (n : ℕ) : ℕ := isqrtAux 256 n n

/-- `s = isqrtN (n · 2^64)` satisfies `s² ≤ n · 2^64 ≤ (s + 1)²`. -/
def sqrtOk (n : ℕ) : Bool :=
  decide (isqrtN (n * 2 ^ 64) ^ 2 ≤ n * 2 ^ 64) && decide (n * 2 ^ 64 ≤ (isqrtN (n * 2 ^ 64) + 1) ^ 2)

/-- Lower bound `s/2^32` on `√n`. -/
def sqrtLoQ (n : ℕ) : ℚ := (isqrtN (n * 2 ^ 64) : ℚ) / 2 ^ 32

/-- Upper bound `(s+1)/2^32` on `√n`. -/
def sqrtHiQ (n : ℕ) : ℚ := ((isqrtN (n * 2 ^ 64) : ℚ) + 1) / 2 ^ 32

theorem sqrt_bounds {n : ℕ} (h : sqrtOk n = true) :
    (sqrtLoQ n : ℝ) ≤ √(n : ℝ) ∧ √(n : ℝ) ≤ sqrtHiQ n := by
  simp only [sqrtOk, Bool.and_eq_true, decide_eq_true_eq] at h
  set s := isqrtN (n * 2 ^ 64)
  have hm : √((n : ℝ) * 2 ^ 64) = √(n : ℝ) * 2 ^ 32 := by
    rw [Real.sqrt_mul (by positivity),
      show (2 : ℝ) ^ 64 = (2 ^ 32) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]
  have h1 : (s : ℝ) ≤ √((n : ℝ) * 2 ^ 64) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast h.1
  have h2 : √((n : ℝ) * 2 ^ 64) ≤ (s : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast h.2
  rw [hm] at h1 h2
  simp only [sqrtLoQ, sqrtHiQ]
  push_cast
  constructor
  · rw [div_le_iff₀ (by positivity)]; exact h1
  · rw [le_div_iff₀ (by positivity)]; exact h2

/-! ## `Γ` -/

/-- Rational lower bound on `Γ`. -/
def gamLo : ℚ := 500371773772050553103 / 2 ^ 199

/-- Rational upper bound on `Γ` (`Gam_le_Q`). -/
def gamHi : ℚ := 7822208915061017503 / 2 ^ 193

theorem gamLo_le : (gamLo : ℝ) ≤ Gam :=
  le_trans (by exact_mod_cast (show gamLo ≤ gammaLoQ 12 by decide +kernel)) gammaLo_le_Gam

theorem le_gamHi : Gam ≤ gamHi := Gam_le_Q

/-! ## Enclosures -/

/-- `r + g Γ + Σ c √n`. -/
structure Enc where
  r : ℚ
  g : ℚ
  s : List (ℚ × ℕ)

/-- `Σ c √n`. -/
noncomputable def sqSum (s : List (ℚ × ℕ)) : ℝ := (s.map fun x => (x.1 : ℝ) * √(x.2 : ℝ)).sum

/-- The value `r + g Γ + Σ c √n`. -/
noncomputable def Enc.val (e : Enc) : ℝ := e.r + e.g * Gam + sqSum e.s

instance : Add Enc := ⟨fun a b => ⟨a.r + b.r, a.g + b.g, a.s ++ b.s⟩⟩

/-- `k · e`. -/
def Enc.smul (k : ℚ) (a : Enc) : Enc := ⟨k * a.r, k * a.g, a.s.map fun x => (k * x.1, x.2)⟩

/-- A rational. -/
def Enc.ofQ (r : ℚ) : Enc := ⟨r, 0, []⟩

theorem sqSum_append (a b : List (ℚ × ℕ)) : sqSum (a ++ b) = sqSum a + sqSum b := by
  simp [sqSum]

theorem sqSum_smul (k : ℚ) (a : List (ℚ × ℕ)) :
    sqSum (a.map fun x => (k * x.1, x.2)) = k * sqSum a := by
  induction a with
  | nil => simp [sqSum]
  | cons x a ih =>
    simp only [sqSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem Enc.val_add (a b : Enc) : (a + b).val = a.val + b.val := by
  show (((a.r + b.r : ℚ) : ℝ) + ((a.g + b.g : ℚ) : ℝ) * Gam + sqSum (a.s ++ b.s)) = _
  rw [sqSum_append, Enc.val, Enc.val]; push_cast; ring

theorem Enc.val_smul (k : ℚ) (a : Enc) : (a.smul k).val = k * a.val := by
  simp only [Enc.val, Enc.smul, sqSum_smul]; push_cast; ring

theorem Enc.val_ofQ (r : ℚ) : (Enc.ofQ r).val = r := by simp [Enc.val, Enc.ofQ, sqSum]

/-- The kernel check: `g ≥ 0`, every `c ≥ 0` and every square root bracketed. -/
def Enc.ok (e : Enc) : Bool :=
  decide (0 ≤ e.g) && e.s.all fun x => decide (0 ≤ x.1) && sqrtOk x.2

/-- Rational lower bound. -/
def Enc.lo (e : Enc) : ℚ := e.r + e.g * gamLo + (e.s.map fun x => x.1 * sqrtLoQ x.2).sum

/-- Rational upper bound. -/
def Enc.hi (e : Enc) : ℚ := e.r + e.g * gamHi + (e.s.map fun x => x.1 * sqrtHiQ x.2).sum

theorem sqSum_bounds {s : List (ℚ × ℕ)} (h : s.all (fun x => decide (0 ≤ x.1) && sqrtOk x.2)) :
    (((s.map fun x => x.1 * sqrtLoQ x.2).sum : ℚ) : ℝ) ≤ sqSum s ∧
      sqSum s ≤ (((s.map fun x => x.1 * sqrtHiQ x.2).sum : ℚ) : ℝ) := by
  induction s with
  | nil => simp [sqSum]
  | cons x s ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hc, hx⟩, hs⟩ := h
    obtain ⟨ih1, ih2⟩ := ih hs
    obtain ⟨h1, h2⟩ := sqrt_bounds hx
    have hc' : (0 : ℝ) ≤ x.1 := by exact_mod_cast hc
    have e1 : sqSum (x :: s) = x.1 * √(x.2 : ℝ) + sqSum s := by
      simp only [sqSum, List.map_cons, List.sum_cons]
    rw [e1, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, Rat.cast_add,
      Rat.cast_add, Rat.cast_mul, Rat.cast_mul]
    exact ⟨add_le_add (mul_le_mul_of_nonneg_left h1 hc') ih1,
      add_le_add (mul_le_mul_of_nonneg_left h2 hc') ih2⟩

theorem Enc.lo_le_val {e : Enc} (h : e.ok = true) : (e.lo : ℝ) ≤ e.val := by
  simp only [Enc.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  have hg : (0 : ℝ) ≤ e.g := by exact_mod_cast h.1
  have h1 := (sqSum_bounds h.2).1
  have h2 := mul_le_mul_of_nonneg_left gamLo_le hg
  have e1 : (e.lo : ℝ) = e.r + e.g * gamLo + ((e.s.map fun x => x.1 * sqrtLoQ x.2).sum : ℚ) := by
    simp only [Enc.lo, Rat.cast_add, Rat.cast_mul]
  rw [e1, Enc.val]; linarith

theorem Enc.val_le_hi {e : Enc} (h : e.ok = true) : e.val ≤ e.hi := by
  simp only [Enc.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  have hg : (0 : ℝ) ≤ e.g := by exact_mod_cast h.1
  have h1 := (sqSum_bounds h.2).2
  have h2 := mul_le_mul_of_nonneg_left le_gamHi hg
  have e1 : (e.hi : ℝ) = e.r + e.g * gamHi + ((e.s.map fun x => x.1 * sqrtHiQ x.2).sum : ℚ) := by
    simp only [Enc.hi, Rat.cast_add, Rat.cast_mul]
  rw [e1, Enc.val]; linarith

/-! ## One-shot certificates -/

/-- `val < 1` from one kernel evaluation. -/
theorem Enc.lt_one {e : Enc} (h : (e.ok && decide (e.hi < 1)) = true) : e.val < 1 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact lt_one_of_Q (Enc.val_le_hi h.1) h.2

/-- `1 ≤ val` from one kernel evaluation. -/
theorem Enc.one_le {e : Enc} (h : (e.ok && decide (1 ≤ e.lo)) = true) : 1 ≤ e.val := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact one_le_of_Q (Enc.lo_le_val h.1) h.2

/-- `val ≤ x` from one kernel evaluation. -/
theorem Enc.le_of {e : Enc} {x : ℚ} (h : (e.ok && decide (e.hi ≤ x)) = true) :
    e.val ≤ x := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (Enc.val_le_hi h.1).trans (by exact_mod_cast h.2)

/-- `x ≤ val` from one kernel evaluation. -/
theorem Enc.ge_of {e : Enc} {x : ℚ} (h : (e.ok && decide (x ≤ e.lo)) = true) :
    (x : ℝ) ≤ e.val := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact (by exact_mod_cast h.2 : (x : ℝ) ≤ e.lo).trans (Enc.lo_le_val h.1)

/-- `A/N ≤ log₂ X ≤ B/N` for `lo ≤ X ≤ hi` with rational `lo > 0`, `2^A ≤ lo^N`, `hi^N ≤ 2^B`. -/
theorem logb_bracket_of_le {X : ℝ} {lo hi : ℚ} {a b : ℝ} (N : ℕ) (hN : 0 < N) (A B : ℤ)
    (ha : a = (A : ℝ) / N) (hb : b = (B : ℝ) / N) (hlo : (lo : ℝ) ≤ X) (hhi : X ≤ hi)
    (h : (decide (0 ≤ lo) && decide ((2 : ℚ) ^ A ≤ lo ^ N) && decide (hi ^ N ≤ (2 : ℚ) ^ B)) =
      true) :
    a ≤ Real.logb 2 X ∧ Real.logb 2 X ≤ b := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact logb_bracket_of_Q hN A B ha hb h.1.1 hlo hhi h.1.2 h.2

/-- `A/N ≤ log₂ val ≤ B/N` from one kernel evaluation. -/
theorem Enc.logb_bracket {e : Enc} (N : ℕ) (hN : 0 < N) (A B : ℤ) {a b : ℝ}
    (ha : a = (A : ℝ) / N) (hb : b = (B : ℝ) / N)
    (h : (e.ok && decide (0 ≤ e.lo) && decide ((2 : ℚ) ^ A ≤ e.lo ^ N) &&
      decide (e.hi ^ N ≤ (2 : ℚ) ^ B)) = true) :
    a ≤ Real.logb 2 e.val ∧ Real.logb 2 e.val ≤ b := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact logb_bracket_of_Q hN A B ha hb h.1.1.2 (Enc.lo_le_val h.1.1.1) (Enc.val_le_hi h.1.1.1)
    h.1.2 h.2

/-! ## Certificates for a real `X = e.val` -/

theorem Enc.lt_one_of_eq {X : ℝ} {e : Enc} (hX : X = e.val)
    (h : (e.ok && decide (e.hi < 1)) = true) : X < 1 := by
  rw [hX]; exact Enc.lt_one h

theorem Enc.one_le_of_eq {X : ℝ} {e : Enc} (hX : X = e.val)
    (h : (e.ok && decide (1 ≤ e.lo)) = true) : 1 ≤ X := by
  rw [hX]; exact Enc.one_le h

theorem Enc.le_of_eq {X : ℝ} {e : Enc} {x : ℚ} (hX : X = e.val)
    (h : (e.ok && decide (e.hi ≤ x)) = true) : X ≤ x := by
  rw [hX]; exact Enc.le_of h

theorem Enc.ge_of_eq {X : ℝ} {e : Enc} {x : ℚ} (hX : X = e.val)
    (h : (e.ok && decide (x ≤ e.lo)) = true) : (x : ℝ) ≤ X := by
  rw [hX]; exact Enc.ge_of h

theorem Enc.logb_bracket_of_eq {X : ℝ} {e : Enc} (hX : X = e.val) (N : ℕ) (hN : 0 < N)
    (A B : ℤ) {a b : ℝ} (ha : a = (A : ℝ) / N) (hb : b = (B : ℝ) / N)
    (h : (e.ok && decide (0 ≤ e.lo) && decide ((2 : ℚ) ^ A ≤ e.lo ^ N) &&
      decide (e.hi ^ N ≤ (2 : ℚ) ^ B)) = true) :
    a ≤ Real.logb 2 X ∧ Real.logb 2 X ≤ b := by
  rw [hX]; exact Enc.logb_bracket N hN A B ha hb h

/-- `X ≤ Y` from one kernel evaluation: `hi(X) ≤ lo(Y)`. -/
theorem Enc.le_le {X Y : ℝ} {e₁ e₂ : Enc} (hX : X = e₁.val) (hY : Y = e₂.val)
    (h : (e₁.ok && e₂.ok && decide (e₁.hi ≤ e₂.lo)) = true) : X ≤ Y := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hX, hY]
  exact (Enc.val_le_hi h.1.1).trans ((by exact_mod_cast h.2 : (e₁.hi : ℝ) ≤ e₂.lo).trans
    (Enc.lo_le_val h.1.2))

/-- `X < Y` from one kernel evaluation: `hi(X) < lo(Y)`. -/
theorem Enc.lt_lt {X Y : ℝ} {e₁ e₂ : Enc} (hX : X = e₁.val) (hY : Y = e₂.val)
    (h : (e₁.ok && e₂.ok && decide (e₁.hi < e₂.lo)) = true) : X < Y := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hX, hY]
  exact (Enc.val_le_hi h.1.1).trans_lt ((by exact_mod_cast h.2 : (e₁.hi : ℝ) < e₂.lo).trans_le
    (Enc.lo_le_val h.1.2))

/-! ## Minima over the forms -/

/-- The forms `e = 1` and `e = 1/2` of the column "minimum" of Table 5. -/
def forms : List Form := [.one, .half]

/-- `x ≤ lo(e)`, checked. -/
def Enc.chkGe (x : ℚ) (e : Enc) : Bool := e.ok && decide (x ≤ e.lo)

theorem Enc.ge_of_chk {X : ℝ} {e : Enc} {x : ℚ} (hX : X = e.val) (h : e.chkGe x = true) :
    (x : ℝ) ≤ X :=
  Enc.ge_of_eq hX h

theorem minF_lt_of_one {f : Form → ℝ} {c : ℝ} (h : f .one < c) : minF f < c :=
  (minF_le_one f).trans_lt h

theorem minF_lt_of_half {f : Form → ℝ} {c : ℝ} (h : f .half < c) : minF f < c :=
  (minF_le_half f).trans_lt h

theorem minF_le_of_one {f : Form → ℝ} {c : ℝ} (h : f .one ≤ c) : minF f ≤ c :=
  (minF_le_one f).trans h

theorem minF_le_of_half {f : Form → ℝ} {c : ℝ} (h : f .half ≤ c) : minF f ≤ c :=
  (minF_le_half f).trans h

/-- A lower bound on the minimum over one place, from one kernel evaluation of both forms. -/
theorem ge_minF1 {f : Form → ℝ} {E : Form → Enc} (hf : ∀ a, f a = (E a).val) {x : ℚ}
    (h : (forms.all fun a => (E a).chkGe x) = true) : (x : ℝ) ≤ minF f := by
  simp only [forms, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact le_minF (Enc.ge_of_chk (hf _) h.1) (Enc.ge_of_chk (hf _) h.2)

/-- A lower bound on the minimum over two places, from one kernel evaluation of the four
combinations. -/
theorem ge_minF2 {f : Form → Form → ℝ} {E : Form → Form → Enc} (hf : ∀ a b, f a b = (E a b).val)
    {x : ℚ} (h : (forms.all fun a => forms.all fun b => (E a b).chkGe x) = true) :
    (x : ℝ) ≤ minF fun a => minF fun b => f a b := by
  simp only [forms, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  exact le_minF (le_minF (Enc.ge_of_chk (hf _ _) h1) (Enc.ge_of_chk (hf _ _) h2))
    (le_minF (Enc.ge_of_chk (hf _ _) h3) (Enc.ge_of_chk (hf _ _) h4))

/-- A lower bound on the minimum over three places, from one kernel evaluation of the eight
combinations. -/
theorem ge_minF3 {f : Form → Form → Form → ℝ} {E : Form → Form → Form → Enc}
    (hf : ∀ a b c, f a b c = (E a b c).val) {x : ℚ}
    (h : (forms.all fun a => forms.all fun b => forms.all fun c => (E a b c).chkGe x) = true) :
    (x : ℝ) ≤ minF fun a => minF fun b => minF fun c => f a b c := by
  simp only [forms, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩ := h
  exact le_minF (le_minF (le_minF (Enc.ge_of_chk (hf _ _ _) h1) (Enc.ge_of_chk (hf _ _ _) h2))
      (le_minF (Enc.ge_of_chk (hf _ _ _) h3) (Enc.ge_of_chk (hf _ _ _) h4)))
    (le_minF (le_minF (Enc.ge_of_chk (hf _ _ _) h5) (Enc.ge_of_chk (hf _ _ _) h6))
      (le_minF (Enc.ge_of_chk (hf _ _ _) h7) (Enc.ge_of_chk (hf _ _ _) h8)))

theorem one_le_minF1 {f : Form → ℝ} {E : Form → Enc} (hf : ∀ a, f a = (E a).val)
    (h : (forms.all fun a => (E a).chkGe 1) = true) : 1 ≤ minF f := by
  simpa using ge_minF1 hf h

theorem one_le_minF2 {f : Form → Form → ℝ} {E : Form → Form → Enc}
    (hf : ∀ a b, f a b = (E a b).val)
    (h : (forms.all fun a => forms.all fun b => (E a b).chkGe 1) = true) :
    1 ≤ minF fun a => minF fun b => f a b := by
  simpa using ge_minF2 hf h

theorem one_le_minF3 {f : Form → Form → Form → ℝ} {E : Form → Form → Form → Enc}
    (hf : ∀ a b c, f a b c = (E a b c).val)
    (h : (forms.all fun a => forms.all fun b => forms.all fun c => (E a b c).chkGe 1) = true) :
    1 ≤ minF fun a => minF fun b => minF fun c => f a b c := by
  simpa using ge_minF3 hf h

end ShrincsSecurity.Concrete.Quantum

end
