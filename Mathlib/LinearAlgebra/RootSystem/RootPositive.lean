/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root-positive bilinear forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
We introduce a Prop-valued mixin class for a root pairing and bilinear form, specifying
reflection-invariance, symmetry, and strict positivity on all roots.  We show that root-positive
forms display the same sign behavior as the canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras.  In the finite case, the canonical polarization yields a root-positive form that is
positive semi-definite on weight space and positive-definite on the span of roots.

## Main definitions:

 * `IsRootPositive`: A prop-valued mixin class for root pairings with bilinear forms, specifying
  the form is symmetric, reflection-invariant, and all roots have strictly positive norm.

## Main results:

* `pairing_pos_iff` and `pairing_zero_iff` : sign relations between `P.pairing` and the form `B`.
* `coxeter_weight_non_neg` : All pairs of roots have non-negative Coxeter weight.
* `orthogonal_of_coxeter_weight_zero` : If Coxeter weight vanishes, then the roots are orthogonal.

## TODO

* Invariance under the Weyl group.

-/

noncomputable section

variable {ι R M N : Type*}

namespace RootPairing

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A Prop-valued class for a bilinear form to be compatible with a root pairing. -/
class IsRootPositive (P : RootPairing ι R M N) (B : M →ₗ[R] M →ₗ[R] R) : Prop where
  zero_lt_apply_root : ∀ i, 0 < B (P.root i) (P.root i)
  symm : ∀ x y, B x y = B y x
  apply_reflection_eq : ∀ i x y, B (P.reflection i x) (P.reflection i y) = B x y

variable {P : RootPairing ι R M N} (B : M →ₗ[R] M →ₗ[R] R) [IsRootPositive P B] (i j : ι)

lemma two_mul_apply_root_root :
    2 * B (P.root i) (P.root j) = P.pairing i j * B (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← IsRootPositive.apply_reflection_eq (P := P) (B := B) j (P.root i) (P.root j)]
  rw [reflection_apply, reflection_apply_self, root_coroot_eq_pairing, LinearMap.map_sub₂,
    LinearMap.map_smul₂, smul_eq_mul, LinearMap.map_neg, LinearMap.map_neg, mul_neg, neg_sub_neg]

@[simp]
lemma zero_lt_apply_root_root_iff : 0 < B (P.root i) (P.root j) ↔ 0 < P.pairing i j := by
  refine ⟨fun h ↦ (mul_pos_iff_of_pos_right
    (IsRootPositive.zero_lt_apply_root (P := P) (B := B) j)).mp ?_,
      fun h ↦ (mul_pos_iff_of_pos_left zero_lt_two).mp ?_⟩
  · rw [← two_mul_apply_root_root]
    exact mul_pos zero_lt_two h
  · rw [two_mul_apply_root_root]
    exact mul_pos h (IsRootPositive.zero_lt_apply_root (P := P) (B := B) j)

lemma zero_lt_pairing_iff : 0 < P.pairing i j ↔ 0 < P.pairing j i := by
  rw [← zero_lt_apply_root_root_iff B, IsRootPositive.symm P, zero_lt_apply_root_root_iff]

lemma coxeterWeight_non_neg : 0 ≤ P.coxeterWeight i j := by
  dsimp [coxeterWeight]
  by_cases h : 0 < P.pairing i j
  · exact le_of_lt <| mul_pos h ((zero_lt_pairing_iff B i j).mp h)
  · have hn : ¬ 0 < P.pairing j i := fun hc ↦ h ((zero_lt_pairing_iff B i j).mpr hc)
    simp_all only [not_lt, ge_iff_le]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

@[simp]
lemma apply_root_root_zero_iff : B (P.root i) (P.root j) = 0 ↔ P.pairing i j = 0 := by
  refine ⟨fun hB => ?_, fun hP => ?_⟩
  · have h2 : 2 * (B (P.root i)) (P.root j) = 0 := mul_eq_zero_of_right 2 hB
    rw [two_mul_apply_root_root] at h2
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (IsRootPositive.zero_lt_apply_root j).ne' h2
  · have h2 : 2 * B (P.root i) (P.root j) = 0 := by rw [two_mul_apply_root_root, hP, zero_mul]
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

lemma pairing_zero_iff : P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  rw [← apply_root_root_zero_iff B, IsRootPositive.symm P, apply_root_root_zero_iff B]

lemma coxeterWeight_zero_iff_isOrthogonal : P.coxeterWeight i j = 0 ↔ P.IsOrthogonal i j := by
  rw [coxeterWeight, mul_eq_zero]
  refine ⟨fun h => ?_, fun h => Or.inl h.1⟩
  rcases h with h | h
  · exact ⟨h, (pairing_zero_iff B i j).mp h⟩
  · exact ⟨(pairing_zero_iff B j i).mp h, h⟩

end RootPairing
