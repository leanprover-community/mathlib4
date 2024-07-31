/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root-positive bilinear forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
We introduce a Prop-valued mixin for classes that admit Weyl-invariant forms such that all roots
have strictly positive norm.  We show that root-positive forms display the same sign behavior as the
canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras.

## Main definitions:

 * `IsRootPositive`: A prop-valued mixin class for root pairings with bilinear forms, specifying
  the form is symmetric, Weyl-invariant, and all roots have strictly positive norm.

## Main results:

* `pairing_pos_iff` and `pairing_zero_iff` : sign relations between `P.pairing` and the form `B`.
* `coxeter_weight_non_neg` : All pairs of roots have non-negative Coxeter weight.
* `orthogonal_of_coxeter_weight_zero` : If Coxeter weight vanishes, then the roots are orthogonal.

-/

noncomputable section

variable {ι R M N : Type*}

namespace RootPairing

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A Prop-valued class for a bilinear form to be compatible with a root system. -/
class IsRootPositive (P : RootPairing ι R M N) (B : M →ₗ[R] M →ₗ[R] R) : Prop where
  root_pos : ∀ i : ι, 0 < B (P.root i) (P.root i)
  symm : ∀ x y : M, B x y = B y x
  refl_inv : ∀ (i : ι) (x y : M), B (P.reflection i x) (P.reflection i y) = B x y

section

variable (P : RootPairing ι R M N) (B : M →ₗ[R] M →ₗ[R] R) [IsRootPositive P B] (i j : ι) (x y : M)

lemma root_positive : 0 < B (P.root i) (P.root i) := IsRootPositive.root_pos i

lemma symmetric : B x y = B y x := IsRootPositive.symm P x y

lemma reflection_invariant (x y : M) : B (P.reflection i x) (P.reflection i y) = B x y :=
  IsRootPositive.refl_inv i x y

end

variable {P : RootPairing ι R M N} (B : M →ₗ[R] M →ₗ[R] R) [IsRootPositive P B] (i j : ι)

lemma two_mul_inner_product :
    2 * B (P.root i) (P.root j) = P.pairing i j * B (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← reflection_invariant P B j (P.root i) (P.root j)]
  rw [reflection_apply, reflection_apply_self, root_coroot_eq_pairing, LinearMap.map_sub₂,
    LinearMap.map_smul₂, smul_eq_mul, LinearMap.map_neg, LinearMap.map_neg, mul_neg, neg_sub_neg]

lemma pairing_pos_iff : 0 < P.pairing i j ↔ 0 < B (P.root i) (P.root j) := by
  refine { mp := fun h => ?_, mpr := fun h => ?_ }
  · have hB : 0 < 2 * B (P.root i) (P.root j) := by
      rw [two_mul_inner_product]
      exact mul_pos h (root_positive P B j)
    rw [two_mul] at hB
    exact pos_add_self_iff.mp hB
  · have hB := mul_pos zero_lt_two h
    rw [two_mul_inner_product] at hB
    exact (mul_pos_iff_of_pos_right (root_positive P B j)).mp hB

lemma pairing_pos_of_pairing_symm_pos (h : 0 < P.pairing i j) : 0 < P.pairing j i := by
  have hB := mul_pos zero_lt_two ((pairing_pos_iff B i j).mp h)
  rw [symmetric P B, two_mul_inner_product] at hB
  exact (mul_pos_iff_of_pos_right (root_positive P B i)).mp hB

lemma coxeter_weight_non_neg : 0 ≤ P.coxeterWeight i j := by
  dsimp [coxeterWeight]
  by_cases h : 0 < P.pairing i j
  · exact le_of_lt <| mul_pos h (pairing_pos_of_pairing_symm_pos B i j h)
  · have hn : ¬ 0 < P.pairing j i := fun hc ↦ h (pairing_pos_of_pairing_symm_pos B j i hc)
    simp_all only [not_lt, ge_iff_le]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

lemma pairing_zero_iff : P.pairing i j = 0 ↔ B (P.root i) (P.root j) = 0 := by
  refine { mp := fun hP => ?_, mpr := fun hB => ?_ }
  · have h2 : 2 * B (P.root i) (P.root j) = 0 := by rw [two_mul_inner_product, hP, zero_mul]
    simp_all only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
  · have h2 : 2 * (B (P.root i)) (P.root j) = 0 := mul_eq_zero_of_right 2 hB
    rw [two_mul_inner_product] at h2
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Ne.symm (ne_of_lt (root_positive P B j))) h2

lemma pairing_zero_of_pairing_symm_zero (h : P.pairing i j = 0) : P.pairing j i = 0 := by
  rw [pairing_zero_iff B, symmetric P B, ← pairing_zero_iff B]
  exact h

lemma orthogonal_of_coxeter_weight_zero (h : P.coxeterWeight i j = 0) : P.IsOrthogonal i j := by
  rw [coxeterWeight, mul_eq_zero] at h
  cases h <;> rename_i h
  · exact ⟨h, pairing_zero_of_pairing_symm_zero B i j h⟩
  · exact ⟨pairing_zero_of_pairing_symm_zero B j i h, h⟩

/-!
lemma root_reflection_trans_iterate' (n : ℕ) :
    ((P.reflection j).trans (P.reflection i))^[n] (P.root i) =
      (2 * n + 1) • P.root i - n • P.pairing i j • P.root j := by
  sorry

-- Get infinitely many roots if Coxeter weight is strictly more than 4. (4 should go in Basic)




I want something flip-invariant.  One common factor in examples: a distinguished subspace on which
the form is non-degenerate.  For finite root data, this is the span of roots.  For Kac-Moody Lie
algebras, this is the extended Cartan (i.e., not just the span of roots.)
So, maybe I want a class with distinguished subspaces `M'` `N'`, paired with each other, with
nondegenerate root-positive forms that are "in correspondence".  Perhaps I just want the images of
`B : M →ₗ[R] N` and `B' : N →ₗ[R] M` to be nondegenerate and root-positive.  So, just trivial
intersection of images with kernels.
-/

/-- This seems to be the structure in common between finite root data and Kac-Moody root systems-/
class DualPositive (P : RootPairing ι R M N) where
  /-- A linear map from weight space to coweight space. -/
  wcw : M →ₗ[R] N
  /-- A linear map from coweight space to weight space. -/
  cww : N →ₗ[R] M
  root_in : ∀ i, P.root i ∈ LinearMap.range cww
  coroot_in : ∀ i, P.coroot i ∈ LinearMap.range wcw
  root_pos : IsRootPositive P (P.toPerfectPairing.toDualRight ∘ₗ wcw)
  coroot_pos : IsRootPositive P.flip (P.toPerfectPairing.toDualLeft ∘ₗ cww)
  weight_nondeg : ∀ x, x ∈ LinearMap.range cww → x ∈ LinearMap.ker wcw → x = 0
  coweight_nondeg : ∀ y, y ∈ LinearMap.range wcw → y ∈ LinearMap.ker cww → y = 0


end RootPairing
