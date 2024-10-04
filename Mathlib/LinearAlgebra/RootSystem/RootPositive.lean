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

section RootPositive

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A Prop-valued class for a bilinear form to be compatible with a root pairing. -/
class IsRootPositive (P : RootPairing ι R M N) (B : M →ₗ[R] M →ₗ[R] R) : Prop where
  zero_lt_apply_root : ∀ i, 0 < B (P.root i) (P.root i)
  symm : ∀ x y, B x y = B y x
  apply_reflection_eq : ∀ i x y, B (P.reflection i x) (P.reflection i y) = B x y

variable {P : RootPairing ι R M N} (B : M →ₗ[R] M →ₗ[R] R) [IsRootPositive P B] (i j : ι)
include B

lemma two_mul_apply_root_root :
    2 * B (P.root i) (P.root j) = P.pairing i j * B (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← IsRootPositive.apply_reflection_eq (P := P) (B := B) j (P.root i) (P.root j)]
  rw [reflection_apply, reflection_apply_self, root_coroot'_eq_pairing, LinearMap.map_sub₂,
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

end RootPositive

section ultraparallel
/-! We consider the case `4 < P.coxeterWeight i j`.  A pair of roots with this configuration
are called `ultraparallel` in the literature.  The reflections in ultraparallel roots generate an
infinite dihedral group, so in particular, any root system with an ultraparallel pair is infinite.

Hmm. If I wait until we do polarization, then it suffices to construct a combination of roots with
nonpositive norm.
-/

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable (P : RootPairing ι R M N) (i j : ι)

/-- This is a function that describes the coefficients attached to `P.root i` and `P.root j` of the
roots given by `(P.reflection i) ∘ (P.reflection j) (P.root i)`. -/
private def refl_coeff : ℕ → R × R
  | .zero => (1,0)
  | n + 1 => (((refl_coeff n).1 + (refl_coeff n).2) * P.coxeterWeight i j - (refl_coeff n).1,
    -(refl_coeff n).1 - (refl_coeff n).2)

lemma refl_coeff_rec (n : ℕ) : ((P.reflection i) ∘ (P.reflection j))
    ((P.refl_coeff i j n).1 • P.root i + (P.refl_coeff i j n).2 • P.pairing i j • P.root j) =
    (P.refl_coeff i j (n + 1)).1 • P.root i +
    (P.refl_coeff i j (n + 1)).2 • P.pairing i j • P.root j := by
  simp only [Function.comp_apply, map_add, LinearMapClass.map_smul, reflection_apply_self, smul_neg,
    map_neg, reflection_apply_root, smul_sub, map_sub, refl_coeff, sub_smul, add_mul, sub_mul,
    add_smul, smul_smul, Int.reduceNeg, neg_smul, one_smul, add_right_inj, neg_sub,
    mul_assoc _ (P.pairing i j)]
  rw [← coxeterWeight, ← sub_eq_zero]
  abel_nf
  simp

lemma refl_coeff_eq (n : ℕ) : (P.refl_coeff i j n).1 • P.root i +
    (P.refl_coeff i j n).2 • P.pairing i j • P.root j =
    ((P.reflection i) ∘ (P.reflection j))^[n] (P.root i) := by
  induction n with
  | zero => simp [refl_coeff]
  | succ n ih =>
    simp only [Function.iterate_succ', ← refl_coeff_rec, ih, Function.comp_apply]

/-!
lemma refl_coeff_ineq_rec_i (n : ℕ) (hi : 0 < (P.refl_coeff i j n).1)
    (hij : -2 * (P.refl_coeff i j n).2 < (P.refl_coeff i j n).1) (hc : 4 < P.coxeterWeight i j) :
    (P.refl_coeff i j n).1 < (P.refl_coeff i j (n + 1)).1 := by
  sorry

lemma refl_coeff_ineq_rec_ij (n : ℕ) (hi : 0 < (P.refl_coeff i j n).1)
    (hij : -2 * (P.refl_coeff i j n).2 < (P.refl_coeff i j n).1) (hc : 4 < P.coxeterWeight i j) :
    -2 * (P.refl_coeff i j (n + 1)).2 < (P.refl_coeff i j (n + 1)).1 := by
  sorry

lemma refl_coeff_ineq_rec_j (n : ℕ) (hi : 0 < (P.refl_coeff i j n).1)
    (hij : -2 * (P.refl_coeff i j n).2 < (P.refl_coeff i j n).1) (hc : 4 < P.coxeterWeight i j) :
    (P.refl_coeff i j (n + 1)).2 < (P.refl_coeff i j n).2 := by
  sorry

lemma refl_coeff_monotone_i : Monotone fun n => (P.refl_coeff i j n).1 := by
  sorry

lemma refl_coeff_monotone_j : Antitone fun n => (P.refl_coeff i j n).2 := by
  sorry


lemma linear_independent_of_four_lt_coxeterWeight (hc : 4 < P.coxeterWeight i j) :
    LinearIndependent R ![P.root i, P.root j] := by
  refine LinearIndependent.pair_iff.mpr fun a b hab => ?_

  sorry
-/

lemma root_reflection_pos_coeff_left {a b : R} (ha : 0 < a) (hab : -2 * b < a)
    (hc : 4 < P.coxeterWeight i j) : a < ((a + b) * P.coxeterWeight i j - a) := by
  have hapb : 2 * a < (a + b) * 4 := by linarith
  have habz : 0 < a + b := by linarith
  have hab4 : (a + b) * 4 < (a + b) * P.coxeterWeight i j := (mul_lt_mul_left habz).mpr hc
  calc
    a = 2 * a - a := by ring
    2 * a - a < (a + b) * 4 - a := sub_lt_sub_right hapb a
    (a + b) * 4 - a < (a + b) * P.coxeterWeight i j - a := sub_lt_sub_right hab4 a
/-!
lemma root_reflection_pos_coeff_right {a b : R} (hab : -2 * b < a) : -(a + b) < b := by
  linarith
-/
lemma root_refl_pos_coeff_right_2 {a b : R} (ha : 0 < a) (hab : -2 * b < a)
    (hc : 4 < P.coxeterWeight i j) : (-2 * -(a + b)) < ((a + b) * P.coxeterWeight i j - a) := by
  have habz : 0 < a + b := by linarith
  have hab4 : (a + b) * 4 < (a + b) * P.coxeterWeight i j := by exact (mul_lt_mul_left habz).mpr hc
  calc
    (-2 * -(a + b)) = 2 * a + 2 * b := by ring
    2 * a + 2 * b < 3 * a + 4 * b := by linarith
    3 * a + 4 * b = ((a + b) * 4 - a) := by ring
    ((a + b) * 4 - a) < ((a + b) * P.coxeterWeight i j - a) := by linarith

-- show coeff of P.root i is monotone!  Or, choose a good linear functional!
/-!
a is positive, and -2 * b < a, so b is bounded below.
P.root i coefficient increases: a < ((a + b) * P.coxeterWeight i j - a)
P.root j coefficient decreases : -(a + b) < b

evaluate at P.coroot i: 2 * a + b * P.pairing j i to
  2 * ((a + b) * P.coxeterWeight i j - a) - (a + b) * P.pairing j i

evaluate at P.coroot j: a * P.pairing i j + 2 * b to
  P.pairing i j * ((a + b) * P.coxeterWeight i j - a) - 2 * (a + b)

try : P.pairing i j * P.coroot i - 2 * P.coroot j
2 * a * P.pairing i j + b * P.coxeterWeight i j - 2 * a * P.pairing i j - 4 * b = b * (c-4) to
2 * ((a + b) * P.cW i j - a) * P.p i j - (a + b) * P.cW i j -
  2 * P.p i j * ((a + b) * P.cW i j - a) + 4 * (a + b) = (a + b) * (4 - c)

Use -P.pairing i j • P.coroot i + 2 • P.coroot j:
get strict increase from -b * (c - 4) to (a + b) * (c - 4)
since 0 < (c - 4) and -b < (a + b)



lemma infinite_of_four_lt_coxeterWeight (hc : 4 < P.coxeterWeight i j) : Infinite ι := by

    --refine monotone_nat_of_le_succ ?_

  refine Infinite.of_injective
    (fun n => (((P.reflection_perm i) ∘ (P.reflection_perm j))^[n] i)) fun m n hmn => ?_
  simp only at hmn
  have h : P.root (((P.reflection_perm j).trans (P.reflection_perm i))^[m] i) =
      P.root (((P.reflection_perm j).trans (P.reflection_perm i))^[n] i) :=
    congrArg (⇑P.root) hmn
  simp only [Equiv.coe_trans, EmbeddingLike.apply_eq_iff_eq] at h

  sorry
-/
  --rw [sub_eq_sub_iff_sub_eq_sub, add_sub_add_right_eq_sub, ← sub_smul, ← sub_smul,
--    ← sub_eq_zero, sub_eq_add_neg, ← neg_smul, smul_smul] at h

-- use reflection_reflection_smul_root_plus_pairing_smul_root
end ultraparallel

/-!
I want something flip-invariant.  One common factor in examples: a distinguished subspace on which
the form is non-degenerate.  For finite root data, this is the span of roots.  For Kac-Moody Lie
algebras, this is the extended Cartan (i.e., not just the span of roots.)
So, maybe I want a class with distinguished subspaces `M'` `N'`, paired with each other, with
nondegenerate root-positive forms that are "in correspondence".  Perhaps I just want the images of
`B : M →ₗ[R] N` and `B' : N →ₗ[R] M` to be nondegenerate and root-positive.  So, just trivial
intersection of images with kernels.
-/

variable [LinearOrderedCommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

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
