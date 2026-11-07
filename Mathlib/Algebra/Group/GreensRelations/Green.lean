/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
module

public import Mathlib.Algebra.Group.GreensRelations.MulSeq
public import Mathlib.Data.Fintype.Card

/-!
# Main Theorems of Green's Relations

This file proves the major structural theorems regarding Green's relations,
including Green's theorem (bijections between H-classes) and regular D-class characterizations.

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/
public section

variable {S : Type*} [Semigroup S]

section MonotonicityAndCommutativity

/-- Equivalence of `L ∘ R` and `R ∘ L` compositions in the definition of Green's `D`-relation. -/
theorem isGreenD_commutes_L_R {a b : S} :
    (∃ c, IsGreenL a c ∧ IsGreenR c b) ↔ (∃ c', IsGreenR a c' ∧ IsGreenL c' b) :=
  ⟨fun ⟨_, hL, hR⟩ ↦ isGreenL_commutes_isGreenR hL hR,
   fun ⟨_, hR, hL⟩ ↦ by
     obtain ⟨z, hRz, hLz⟩ := isGreenL_commutes_isGreenR hL.symm hR.symm
     exact ⟨z, hLz.symm, hRz.symm⟩⟩

end MonotonicityAndCommutativity

section RegularDClassesCharacterizations

/-- A `D`-class is regular if and only if it contains an idempotent. -/
theorem isRegularDClass_iff_exists_idempotent (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∃ e ∈ D, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · intro hReg
    obtain ⟨s, hs⟩ := hReg x₀ (IsGreenD.refl x₀)
    exact ⟨x₀ * s, ⟨x₀ * s, IsGreenL.refl _, ⟨Or.inr ⟨s, rfl⟩, Or.inr ⟨x₀, hs.symm⟩⟩⟩,
      by rw [← mul_assoc, hs]⟩
  · rintro ⟨e, heD, he_idem⟩ y hyD
    let ⟨z, hL_yz, hR_ze⟩ := hyD.trans heD.symm
    have h_ez_z : e * z = z := by
      rcases hR_ze.left with rfl | ⟨v, rfl⟩
      · exact he_idem
      · rw [← mul_assoc, he_idem]
    obtain ⟨u, hu_z⟩ : ∃ u, z * u * z = z := by
      rcases hR_ze.right with rfl | ⟨u, rfl⟩
      · exact ⟨e, by rw [he_idem, he_idem]⟩
      · exact ⟨u, h_ez_z⟩
    have hy_uz : y * u * z = y := by
      rcases hL_yz.left with rfl | ⟨p, rfl⟩
      · exact hu_z
      · rw [mul_assoc p, mul_assoc, hu_z]
    rcases hL_yz.right with rfl | ⟨q, rfl⟩
    · exact ⟨u, hy_uz⟩
    · exact ⟨u * q, by simpa [mul_assoc] using hy_uz⟩

/-- A `D`-class is regular if and only if every `L`-class inside it contains an idempotent. -/
theorem isRegularDClass_iff_forall_LClass_has_idempotent
    (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∀ L : Set S, (∃ x ∈ D, L = IsGreenL.eqvClass x) → ∃ e ∈ L, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · rintro hReg L ⟨x, hx, rfl⟩
    exact MulSeq.exists_idempotent_in_greenL_of_regular (hReg x hx)
  · intro H x hx
    obtain ⟨e, he, he_idem⟩ := H (IsGreenL.eqvClass x) ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, e = u * x := by
      rcases he.left with h | ⟨u, hu⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨u, hu⟩
    obtain ⟨v, hv⟩ : ∃ v, x = v * e := by
      rcases he.right with h | ⟨v, hv⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨v, hv⟩
    exact ⟨u, by rw [mul_assoc, ← hu, hv, mul_assoc, he_idem]⟩

/-- A `D`-class is regular if and only if every `R`-class inside it contains an idempotent. -/
theorem isRegularDClass_iff_forall_RClass_has_idempotent
    (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) :
    IsRegularDClass D ↔ ∀ R : Set S, (∃ x ∈ D, R = IsGreenR.eqvClass x) → ∃ e ∈ R, e * e = e := by
  obtain ⟨x₀, rfl⟩ := hD
  constructor
  · rintro hReg R ⟨x, hx, rfl⟩
    exact MulSeq.exists_idempotent_in_greenR_of_regular (hReg x hx)
  · intro H x hx
    obtain ⟨e, he, he_idem⟩ := H (IsGreenR.eqvClass x) ⟨x, hx, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, e = x * u := by
      rcases he.left with h | ⟨u, hu⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨u, hu⟩
    obtain ⟨v, hv⟩ : ∃ v, x = e * v := by
      rcases he.right with h | ⟨v, hv⟩
      · exact ⟨e, by exact h ▸ he_idem.symm⟩
      · exact ⟨v, hv⟩
    exact ⟨u, by rw [← hu, hv, ← mul_assoc, he_idem]⟩

end RegularDClassesCharacterizations

section BijectionsAndCardinalities

/-- A bijection between the `H`-classes of two `L`-related elements. -/
noncomputable def equivHClassOfIsGreenL {a b : S} (h_L_ab : IsGreenL a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b := by
  by_cases ha_eq_b : a = b
  · exact ha_eq_b ▸ Equiv.refl _
  · choose w hw using h_L_ab.left.resolve_left ha_eq_b
    choose z hz using h_L_ab.right.resolve_left (Ne.symm ha_eq_b)
    have hwza : w * z * a = a := by simp only [mul_assoc, ← hz, ← hw]
    have hzwb : z * w * b = b := by simp only [mul_assoc, ← hw, ← hz]
    exact {
      toFun := fun ⟨x, hL, hR⟩ ↦ ⟨z * x, ⟨IsGreenL.trans ⟨Or.inr ⟨z, rfl⟩,
        Or.inr ⟨w, by simpa [← mul_assoc] using (IsGreenR.cancellation hR hwza).symm⟩⟩
        (hL.trans h_L_ab), hz.symm ▸ IsGreenR.mul_left z hR⟩⟩
      invFun := fun ⟨y, hL, hR⟩ ↦ ⟨w * y, ⟨IsGreenL.trans ⟨Or.inr ⟨w, rfl⟩,
        Or.inr ⟨z, by simpa [← mul_assoc] using (IsGreenR.cancellation hR hzwb).symm⟩⟩
        (hL.trans h_L_ab.symm), hw.symm ▸ IsGreenR.mul_left w hR⟩⟩
      left_inv := fun ⟨x, _, hR⟩ ↦ Subtype.ext <| by
        simpa [← mul_assoc] using IsGreenR.cancellation hR hwza
      right_inv := fun ⟨y, _, hR⟩ ↦ Subtype.ext <| by
        simpa [← mul_assoc] using IsGreenR.cancellation hR hzwb
    }

open MulOpposite in
/-- A bijection between the `H`-classes of two `R`-related elements. -/
noncomputable def equivHClassOfIsGreenR {a b : S} (h : IsGreenR a b) :
    IsGreenH.eqvClass a ≃ IsGreenH.eqvClass b :=
  (IsGreenH.equivHClassOp a).trans
      ((equivHClassOfIsGreenL (isGreenR_iff_isGreenL_op.mp h)).trans
      (IsGreenH.equivHClassOp b).symm)

open Classical in
/-- Any two `H`-classes within the same `D`-class have the same cardinality. -/
theorem card_greenHClass_eq_of_isGreenD [Fintype S] {a b : S} (h : IsGreenD a b) :
    Fintype.card (IsGreenH.eqvClass a) = Fintype.card (IsGreenH.eqvClass b) :=
  let ⟨_, hL, hR⟩ := h
  Eq.trans (Fintype.card_congr (equivHClassOfIsGreenL hL))
    (Fintype.card_congr (equivHClassOfIsGreenR hR))

end BijectionsAndCardinalities
