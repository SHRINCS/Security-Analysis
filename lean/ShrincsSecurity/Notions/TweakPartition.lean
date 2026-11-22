module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Set.Insert

/-!
# Exclusive tweak partitions

Main paper, Section 4.2, **Definition 4.7** (SM-TCR-EXCL), the tweak data: a disjoint partition
`T = T₁ ∪ T₂ ∪ T₃` with `|T₂| = |T₃|` and a bijection `ω : T₂ → T₃`.

We encode the partition and the bijection by one involution `partner : T → T`, which is `ω` on
`T₂`, `ω⁻¹` on `T₃` and the identity on `T₁`, together with the class map `cls`. The data are
equivalent to the paper's (`ExclusiveTweaks.omega` recovers `ω` as an equivalence `T₂ ≃ T₃`, and
`ExclusiveTweaks.ofOmega` builds the structure from a partition and a bijection). The point of
the encoding is that every guard and every winning clause of Definition 4.7 is phrased through the
set `Ω(T) = {T, partner T}` of tweaks at which a collision with a challenge at `T` is accepted
(the set `Ω(T)` of the proof of Theorem E.1): the paper's three case distinctions collapse to a
single membership test (`ExclusiveTweaks.mem_Omega_iff_cases`).
-/

@[expose] public section

namespace ShrincsSecurity.Notions

/-- The three parts of the tweak space of Definition 4.7. -/
inductive TweakClass
  /-- `T₁`: tweaks without a partner. -/
  | one
  /-- `T₂`: the domain of `ω` (in SHRINCS, internal-node addresses). -/
  | two
  /-- `T₃`: the range of `ω` (in SHRINCS, WOTS+C public-key-compression addresses). -/
  | three
deriving DecidableEq, Repr

/-- The class of `partner t` given the class of `t`: `T₂` and `T₃` are swapped. -/
def TweakClass.swap : TweakClass → TweakClass
  | .one => .one
  | .two => .three
  | .three => .two

@[simp] theorem TweakClass.swap_swap (c : TweakClass) : c.swap.swap = c := by
  cases c <;> rfl

/-- **Definition 4.7, tweak data.** A partition `T = T₁ ∪ T₂ ∪ T₃` (`cls`) with a bijection
`ω : T₂ → T₃`, encoded by the involution `partner` (`ω` on `T₂`, `ω⁻¹` on `T₃`, the identity on
`T₁`). -/
structure ExclusiveTweaks (T : Type) where
  /-- The part of the partition a tweak belongs to. -/
  cls : T → TweakClass
  /-- `ω` on `T₂`, `ω⁻¹` on `T₃`, the identity on `T₁`. -/
  partner : T → T
  /-- `partner` is an involution. -/
  partner_partner : ∀ t, partner (partner t) = t
  /-- `partner` swaps `T₂` and `T₃` and preserves `T₁`. -/
  cls_partner : ∀ t, cls (partner t) = (cls t).swap
  /-- `partner` is the identity on `T₁`. -/
  partner_of_one : ∀ t, cls t = .one → partner t = t

namespace ExclusiveTweaks

variable {T : Type} (X : ExclusiveTweaks T)

/-- `Ω(T)`: the tweaks at which Definition 4.7 accepts a collision with a challenge at `T`
(proof of Theorem E.1). -/
def Omega (t : T) : Set T := {t, X.partner t}

instance [DecidableEq T] (t t' : T) : Decidable (t' ∈ X.Omega t) :=
  inferInstanceAs (Decidable (t' = t ∨ t' = X.partner t))

theorem mem_Omega_iff (t t' : T) : t' ∈ X.Omega t ↔ t' = t ∨ t' = X.partner t := Iff.rfl

theorem self_mem_Omega (t : T) : t ∈ X.Omega t := Or.inl rfl

/-- `Ω` is symmetric: `t' ∈ Ω(t) ↔ t ∈ Ω(t')`. -/
theorem mem_Omega_comm (t t' : T) : t' ∈ X.Omega t ↔ t ∈ X.Omega t' := by
  simp only [mem_Omega_iff]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (X.partner_partner t).symm
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (X.partner_partner t').symm

/-- Two sets `Ω(t)`, `Ω(t')` meet only when they are equal, which happens exactly when
`t' ∈ Ω(t)`. This is the disjointness of the sets `Ω(Tᵢ)` of distinct admitted challenges used in
the proof of Theorem E.1. -/
theorem Omega_eq_of_mem {t t' : T} (h : t' ∈ X.Omega t) : X.Omega t' = X.Omega t := by
  rcases h with rfl | rfl
  · rfl
  · ext u
    simp only [mem_Omega_iff, X.partner_partner]
    exact Or.comm

theorem mem_Omega_of_mem_of_mem {t t' u : T} (h : u ∈ X.Omega t) (h' : u ∈ X.Omega t') :
    t' ∈ X.Omega t := by
  have h1 := X.Omega_eq_of_mem h
  have h2 := X.Omega_eq_of_mem h'
  rw [← h1, h2]
  exact X.self_mem_Omega t'

/-- The three admissibility clauses of Definition 4.7 (steps 6–8) are membership in `Ω(Tⱼ)`. -/
theorem mem_Omega_iff_cases (tj t : T) :
    t ∈ X.Omega tj ↔
      (X.cls tj = .one → t = tj) ∧
      (X.cls tj = .two → t = tj ∨ t = X.partner tj) ∧
      (X.cls tj = .three → t = tj ∨ t = X.partner tj) := by
  rw [mem_Omega_iff]
  cases h : X.cls tj
  · simp [X.partner_of_one tj h]
  · simp
  · simp

theorem partner_ne_of_cls_ne_one {t : T} (h : X.cls t ≠ .one) : X.partner t ≠ t := by
  intro he
  have := X.cls_partner t
  rw [he] at this
  cases hc : X.cls t with
  | one => exact h hc
  | two => rw [hc] at this; exact absurd this (by decide)
  | three => rw [hc] at this; exact absurd this (by decide)

/-- The bijection `ω : T₂ ≃ T₃` of Definition 4.7. -/
def omega : {t // X.cls t = .two} ≃ {t // X.cls t = .three} where
  toFun t := ⟨X.partner t.1, by rw [X.cls_partner, t.2]; rfl⟩
  invFun t := ⟨X.partner t.1, by rw [X.cls_partner, t.2]; rfl⟩
  left_inv t := Subtype.ext (X.partner_partner t.1)
  right_inv t := Subtype.ext (X.partner_partner t.1)

@[simp] theorem omega_apply (t : {t // X.cls t = .two}) : (X.omega t).1 = X.partner t.1 := rfl

/-- Build the tweak data from a partition `cls` and a bijection `ω : T₂ ≃ T₃`. -/
noncomputable def ofOmega (cls : T → TweakClass)
    (ω : {t // cls t = .two} ≃ {t // cls t = .three}) : ExclusiveTweaks T := by
  classical
  exact
  { cls := cls
    partner := fun t =>
      if h2 : cls t = .two then (ω ⟨t, h2⟩).1
      else if h3 : cls t = .three then (ω.symm ⟨t, h3⟩).1 else t
    partner_partner := by
      intro t
      by_cases h2 : cls t = .two
      · have h3 : cls (ω ⟨t, h2⟩).1 = .three := (ω ⟨t, h2⟩).2
        have h2' : cls (ω ⟨t, h2⟩).1 ≠ .two := by rw [h3]; decide
        simp [h2, h3]
      · by_cases h3 : cls t = .three
        · have h2'' : cls (ω.symm ⟨t, h3⟩).1 = .two := (ω.symm ⟨t, h3⟩).2
          simp [h3, h2'']
        · simp [h2, h3]
    cls_partner := by
      intro t
      by_cases h2 : cls t = .two
      · simp [h2, (ω ⟨t, h2⟩).2, TweakClass.swap]
      · by_cases h3 : cls t = .three
        · simp [h3, (ω.symm ⟨t, h3⟩).2, TweakClass.swap]
        · simp only [h2, h3, ↓reduceDIte]
          cases hc : cls t with
          | one => rfl
          | two => exact absurd hc h2
          | three => exact absurd hc h3
    partner_of_one := by
      intro t h
      simp [h] }

/-- The trivial instance `T = T₁`: no tweak has a partner, and SM-TCR-EXCL is SM-TCR. -/
def trivial (T : Type) : ExclusiveTweaks T where
  cls _ := .one
  partner := id
  partner_partner _ := rfl
  cls_partner _ := rfl
  partner_of_one _ _ := rfl

end ExclusiveTweaks

end ShrincsSecurity.Notions

end
