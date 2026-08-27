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

/-- tbd -/
@[mk_iff] class IsHeckeTriple : Prop where
  degreeNeZero : (DoubleCoset.mk H₁ H₂ g).degree ≠ 0

noncomputable instance [IsHeckeTriple H₁ H₂ g] : Fintype (DecompQuotient H₁ H₂ g) :=
  Subgroup.fintypeOfIndexNeZero IsHeckeTriple.degreeNeZero

instance instIsHeckeTriple_diag_one (H : Subgroup G) : IsHeckeTriple H H 1 := ⟨by simp⟩

instance instIsHeckeTriple_mulLeft [IsHeckeTriple H₁ H₂ g] (h₁ : H₁) :
    IsHeckeTriple H₁ H₂ (h₁ * g) := by
  have := (DoubleCoset.eq H₁ H₂ (h₁ * g) g).mpr ⟨h₁⁻¹, H₁.inv_mem h₁.prop, 1, H₂.one_mem, by simp⟩
  simp [isHeckeTriple_iff, this, mk_degree]

instance instIsHeckeTriple_mulRight [IsHeckeTriple H₁ H₂ g] (h₂ : H₂) :
    IsHeckeTriple H₁ H₂ (g * h₂) := by
  have := (DoubleCoset.eq H₁ H₂ (g * h₂) g).mpr ⟨1, H₁.one_mem, h₂⁻¹, H₂.inv_mem h₂.prop, by simp⟩
  simp [isHeckeTriple_iff, this, mk_degree]

lemma isHeckeTriple_trans [IsHeckeTriple H₁ H₂ g] [IsHeckeTriple H₂ H₃ g'] :
    IsHeckeTriple H₁ H₃ (g * g') := by
  have h₂₃ : ((ConjAct.toConjAct g) • ((ConjAct.toConjAct g') • H₃)).relIndex
      ((ConjAct.toConjAct g) • H₂) ≠ 0 := by
    simp [Subgroup.relIndex_pointwise_smul, ← DecompQuotient.nat_card_eq_relIndex]
  simpa [isHeckeTriple_iff, DecompQuotient.nat_card_eq_relIndex, mul_smul, mk_degree] using
    Subgroup.relIndex_ne_zero_trans h₂₃ IsHeckeTriple.degreeNeZero

instance instIsHeckeTriple_trans [IsHeckeTriple H₁ H₂ g]
    [IsHeckeTriple H₂ H₃ g'] (h₂ : H₂) : IsHeckeTriple H₁ H₃ (g * h₂ * g') :=
  isHeckeTriple_trans H₁ H₂ H₃ (g * h₂) g'

instance instIsHeckeTriple_diag_mul (H : Subgroup G) (g g' : G)
    [IsHeckeTriple H H g] [IsHeckeTriple H H g'] : IsHeckeTriple H H (g * g') := by
  simpa using isHeckeTriple_trans H H H g g'

end triple

/-- tbd -/
@[implicit_reducible]
def HeckeCoset := {x : DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G) // x.degree ≠ 0}

instance : Coe (HeckeCoset H₁ H₂) (DoubleCoset.Quotient (H₁ : Set G) (H₂ : Set G)) := ⟨Subtype.val⟩

namespace HeckeCoset

variable {H₁ H₂ H₃}

/-- tbd -/
noncomputable def rep (x : HeckeCoset H₁ H₂) : G := x.val.out

lemma rep_eq_out (x : HeckeCoset H₁ H₂) : x.rep = x.val.out := rfl

/-- tbd -/
noncomputable abbrev degree (x : HeckeCoset H₁ H₂) : ℕ := x.val.degree

@[simp]
lemma degree_ne_zero (x : HeckeCoset H₁ H₂) :
    x.degree ≠ 0 := x.prop

lemma degree_eq_rep (x : HeckeCoset H₁ H₂) :
    x.degree = Nat.card (DoubleCoset.DecompQuotient H₁ H₂ x.rep) := by
  simp [degree, rep_eq_out, ← DoubleCoset.degree_eq_out]

instance (x : HeckeCoset H₁ H₂) : IsHeckeTriple H₁ H₂ x.rep := by
  simp [isHeckeTriple_iff, rep_eq_out, DoubleCoset.mk_degree, ← DoubleCoset.degree_eq_out]

/-- tbd -/
abbrev mk (H₁ H₂ : Subgroup G) (g : G) [IsHeckeTriple H₁ H₂ g] :
    HeckeCoset H₁ H₂ := ⟨DoubleCoset.mk H₁ H₂ g, IsHeckeTriple.degreeNeZero⟩

lemma coe_mk (g : G) [IsHeckeTriple H₁ H₂ g] :
    mk H₁ H₂ g = DoubleCoset.mk H₁ H₂ g := rfl

@[simp]
lemma mk_rep (x : HeckeCoset H₁ H₂) :
    mk H₁ H₂ x.rep = x := by
  simp [mk, rep_eq_out, DoubleCoset.out_eq']

lemma mk_degree [IsHeckeTriple H₁ H₂ g] :
    (mk H₁ H₂ g).degree = Nat.card (DoubleCoset.DecompQuotient H₁ H₂ g) := by
  simp [degree, DoubleCoset.mk_degree]

lemma mk_eq_iff {g g' : G} [IsHeckeTriple H₁ H₂ g] [IsHeckeTriple H₁ H₂ g'] :
    mk H₁ H₂ g = mk H₁ H₂ g' ↔ ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g' = h₁ * g * h₂ := by
  rw [Subtype.ext_iff, DoubleCoset.eq]

@[simp]
lemma diag_mk_one_rep_mem (H : Subgroup G) : (mk H H 1).rep ∈ H := by
  obtain ⟨_, h₁, _, h₂, heq⟩ :=
    HeckeCoset.mk_eq_iff.mp (show mk H H 1 = mk H H (mk H H 1).rep from by simp)
  simp [heq, H.mul_mem h₁ h₂]

@[simp]
lemma diag_one_degree_eq_one (H : Subgroup G) : (mk H H 1).degree = 1 := by
  rw [mk_degree, DoubleCoset.DecompQuotient.nat_card_eq_relIndex]
  simp

lemma induction_on (x : HeckeCoset H₁ H₂) {p : HeckeCoset H₁ H₂ → Prop}
    (h : ∀ (g : G) [IsHeckeTriple H₁ H₂ g], p (mk H₁ H₂ g)) :
    p x := by
  rw [← mk_rep x]
  exact h x.rep

end HeckeCoset
