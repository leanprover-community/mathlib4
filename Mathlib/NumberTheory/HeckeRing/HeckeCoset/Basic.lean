/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Jiaxi Mo
-/
module

public import Mathlib.NumberTheory.HeckeRing.HeckeCoset.DecompQuotient

/-!
# Hecke Double Cosets

-/

@[expose] public section

variable {G : Type*} [Group G] (H₁ H₂ H₃ : Subgroup G) (g g' : G)

open Pointwise

section triple

open DoubleCoset

/-- `(H₁, H₂, g)` is a Hecke triple if `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` is finite. -/
@[mk_iff] class IsHeckeFinite : Prop where
  degreeNeZero : (DoubleCoset.mk H₁ H₂ g).degree ≠ 0

noncomputable instance [IsHeckeFinite H₁ H₂ g] : Fintype (DecompQuotient H₁ H₂ g) :=
  Subgroup.fintypeOfIndexNeZero IsHeckeFinite.degreeNeZero

instance instIsHeckeFinite_diag_one (H : Subgroup G) : IsHeckeFinite H H 1 := ⟨by simp⟩

instance instIsHeckeFinite_mulLeft [IsHeckeFinite H₁ H₂ g] (h₁ : H₁) :
    IsHeckeFinite H₁ H₂ (h₁ * g) := by
  have := (DoubleCoset.eq H₁ H₂ (h₁ * g) g).mpr ⟨h₁⁻¹, H₁.inv_mem h₁.prop, 1, H₂.one_mem, by simp⟩
  simp [isHeckeFinite_iff, this, mk_degree]

instance instIsHeckeFinite_mulRight [IsHeckeFinite H₁ H₂ g] (h₂ : H₂) :
    IsHeckeFinite H₁ H₂ (g * h₂) := by
  have := (DoubleCoset.eq H₁ H₂ (g * h₂) g).mpr ⟨1, H₁.one_mem, h₂⁻¹, H₂.inv_mem h₂.prop, by simp⟩
  simp [isHeckeFinite_iff, this, mk_degree]

lemma isHeckeFinite_trans [IsHeckeFinite H₁ H₂ g] [IsHeckeFinite H₂ H₃ g'] :
    IsHeckeFinite H₁ H₃ (g * g') := by
  have h₂₃ : ((ConjAct.toConjAct g) • ((ConjAct.toConjAct g') • H₃)).relIndex
      ((ConjAct.toConjAct g) • H₂) ≠ 0 := by
    simp [Subgroup.relIndex_pointwise_smul, ← DecompQuotient.nat_card_eq_relIndex]
  simpa [isHeckeFinite_iff, DecompQuotient.nat_card_eq_relIndex, mul_smul, mk_degree] using
    Subgroup.relIndex_ne_zero_trans h₂₃ IsHeckeFinite.degreeNeZero

instance instIsHeckeFinite_trans [IsHeckeFinite H₁ H₂ g]
    [IsHeckeFinite H₂ H₃ g'] (h₂ : H₂) : IsHeckeFinite H₁ H₃ (g * h₂ * g') :=
  isHeckeFinite_trans H₁ H₂ H₃ (g * h₂) g'

instance instIsHeckeFinite_diag_mul (H : Subgroup G) (g g' : G)
    [IsHeckeFinite H H g] [IsHeckeFinite H H g'] : IsHeckeFinite H H (g * g') := by
  simpa using isHeckeFinite_trans H H H g g'

end triple

/-- The collection of double cosets admitting finite decomposition into left cosets. -/
@[implicit_reducible]
def DoubleCoset₀ := {x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G) // x.degree ≠ 0}

instance : Coe (DoubleCoset₀ H₁ H₂) (DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) :=
  ⟨Subtype.val⟩

namespace DoubleCoset₀

variable {H₁ H₂ H₃}

/-- A representative of the underlying double coset in the ambient group. -/
noncomputable def rep (x : DoubleCoset₀ H₁ H₂) : G := x.val.out

lemma rep_eq_out (x : DoubleCoset₀ H₁ H₂) : x.rep = x.val.out := rfl

/-- The cardinality of `H₁ ⧸ (H₁ ∩ gH₂g⁻¹)` where `g` is a representative of the underlying double
coset. -/
noncomputable abbrev degree (x : DoubleCoset₀ H₁ H₂) : ℕ := x.val.degree

@[simp]
lemma degree_ne_zero (x : DoubleCoset₀ H₁ H₂) :
    x.degree ≠ 0 := x.prop

lemma degree_eq_rep (x : DoubleCoset₀ H₁ H₂) :
    x.degree = Nat.card (DoubleCoset.DecompQuotient H₁ H₂ x.rep) := by
  simp [degree, rep_eq_out, ← DoubleCoset.degree_eq_out]

instance (x : DoubleCoset₀ H₁ H₂) : IsHeckeFinite H₁ H₂ x.rep := by
  simp [isHeckeFinite_iff, rep_eq_out, DoubleCoset.mk_degree, ← DoubleCoset.degree_eq_out]

/-- The Hecke double coset represented by `g`. -/
abbrev mk (H₁ H₂ : Subgroup G) (g : G) [IsHeckeFinite H₁ H₂ g] :
    DoubleCoset₀ H₁ H₂ := ⟨DoubleCoset.mk H₁ H₂ g, IsHeckeFinite.degreeNeZero⟩

lemma coe_mk (g : G) [IsHeckeFinite H₁ H₂ g] :
    mk H₁ H₂ g = DoubleCoset.mk H₁ H₂ g := rfl

@[simp]
lemma mk_rep (x : DoubleCoset₀ H₁ H₂) :
    mk H₁ H₂ x.rep = x := by
  simp [mk, rep_eq_out, DoubleCoset.out_eq']

lemma mk_degree [IsHeckeFinite H₁ H₂ g] :
    (mk H₁ H₂ g).degree = Nat.card (DoubleCoset.DecompQuotient H₁ H₂ g) := by
  simp [degree, DoubleCoset.mk_degree]

lemma mk_eq_iff {g g' : G} [IsHeckeFinite H₁ H₂ g] [IsHeckeFinite H₁ H₂ g'] :
    mk H₁ H₂ g = mk H₁ H₂ g' ↔ ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g' = h₁ * g * h₂ := by
  rw [Subtype.ext_iff, DoubleCoset.eq]

@[simp]
lemma diag_mk_one_rep_mem (H : Subgroup G) : (mk H H 1).rep ∈ H := by
  obtain ⟨_, h₁, _, h₂, heq⟩ := mk_eq_iff.mp (show mk H H 1 = mk H H (mk H H 1).rep from by simp)
  simp [heq, H.mul_mem h₁ h₂]

@[simp]
lemma diag_one_degree_eq_one (H : Subgroup G) : (mk H H 1).degree = 1 := by
  rw [mk_degree, DoubleCoset.DecompQuotient.nat_card_eq_relIndex]
  simp

lemma induction_on (x : DoubleCoset₀ H₁ H₂) {p : DoubleCoset₀ H₁ H₂ → Prop}
    (h : ∀ (g : G) [IsHeckeFinite H₁ H₂ g], p (mk H₁ H₂ g)) :
    p x := by
  rw [← mk_rep x]
  exact h x.rep

end DoubleCoset₀
