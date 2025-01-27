/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root-positive bilinear forms on root pairings

-- TODO Adjust this doc string after code changes complete

This file contains basic results on Weyl-invariant inner products for root systems and root data.
We introduce a Prop-valued mixin class for a root pairing and bilinear form, specifying
reflection-invariance, symmetry, and strict positivity on all roots.  We show that root-positive
forms display the same sign behavior as the canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras.  In the finite case, the canonical polarization yields a root-positive form that is
positive semi-definite on weight space and positive-definite on the span of roots.

## Main definitions:

 * `RootPositiveForm`: A prop-valued mixin class for root pairings with bilinear forms, specifying
  the form is symmetric, reflection-invariant, and all roots have strictly positive norm.

## Main results:

* `pairing_pos_iff` and `pairing_zero_iff` : sign relations between `P.pairing` and the form `B`.
* `coxeter_weight_non_neg` : All pairs of roots have non-negative Coxeter weight.
* `orthogonal_of_coxeter_weight_zero` : If Coxeter weight vanishes, then the roots are orthogonal.

## TODO

* Invariance under the Weyl group.

-/

noncomputable section

open Function Set Submodule

variable {ι R S M N : Type*}

namespace RootPairing

variable [LinearOrderedCommRing S] [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M]
  [AddCommGroup N] [Module R N]

variable (S) in
/-- Given a root pairing, this is an invariant symmetric bilinear form satisfying a positivity
condition. -/
structure RootPositiveForm (P : RootPairing ι R M N) [P.IsValuedIn S] where
  /-- The bilinear form bundled inside a `RootPositiveForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  apply_reflection_eq (i : ι) (x y : M) : form (P.reflection i x) (P.reflection i y) = form x y
  exists_pos_eq (i : ι) : ∃ s > 0, algebraMap S R s = form (P.root i) (P.root i)
  exists_eq (i j : ι) : ∃ s, algebraMap S R s = form (P.root i) (P.root j)

variable {P : RootPairing ι R M N} [P.IsValuedIn S] (B : P.RootPositiveForm S) (i j : ι)
  [FaithfulSMul S R]

omit [Module S M] [IsScalarTower S R M] [FaithfulSMul S R] in
lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← B.apply_reflection_eq j]
  rw [reflection_apply, reflection_apply_self, root_coroot'_eq_pairing, LinearMap.map_sub₂,
    LinearMap.map_smul₂, smul_eq_mul, LinearMap.map_neg, LinearMap.map_neg, mul_neg, neg_sub_neg]

omit [Module S M] [IsScalarTower S R M] in
lemma RootPositiveForm.form_apply_root_ne_zero (i : ι) :
    B.form (P.root i) (P.root i) ≠ 0 := by
  obtain ⟨s, hs, hs'⟩ := B.exists_pos_eq i
  simpa [← hs'] using hs.ne'

/-- Given a root-positive form associated to a root pairing with coefficients in `R` but taking
values in `S`, this is the associated `S`-bilinear form on the `S`-span of the roots. -/
def RootPositiveForm.formIn :
    LinearMap.BilinForm S (span S (range P.root)) :=
  LinearMap.restrictScalarsRange (span S (range P.root)).subtype (span S (range P.root)).subtype
  (Algebra.linearMap S R) (FaithfulSMul.injective_algebraMap S R) B.form
  (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (s := range P.root) (t := range P.root)
      (B := (LinearMap.restrictScalarsₗ S R _ _ _).comp (B.form.restrictScalars S))
    · rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
      simpa using B.exists_eq i j
    · simpa
    · simpa)

@[simp] lemma RootPositiveForm.algebraMap_formIn {x y : span S (range P.root)} :
    algebraMap S R (B.formIn x y) = B.form x y := by
  change Algebra.linearMap S R _ = _
  simp [formIn]

lemma RootPositiveForm.algebraMap_apply_eq_form_iff {x y : span S (range P.root)} {s : S} :
    algebraMap S R s = B.form x y ↔ s = B.formIn x y := by
  simp [formIn]

lemma RootPositiveForm.zero_lt_formIn_iff {x y : span S (range P.root)} :
    0 < B.formIn x y ↔ ∃ s > 0, algebraMap S R s = B.form x y := by
  refine ⟨fun h ↦ ⟨B.formIn x y, h, by simp⟩, fun ⟨s, h, h'⟩ ↦ ?_⟩
  rw [← B.algebraMap_formIn] at h'
  rwa [← FaithfulSMul.injective_algebraMap S R h']

lemma RootPositiveForm.zero_lt_formIn_apply_root (i : ι)
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i)) :
    0 < B.formIn ⟨P.root i, hi⟩ ⟨P.root i, hi⟩ := by
  simpa only [zero_lt_formIn_iff] using B.exists_pos_eq i

lemma RootPositiveForm.isSymm_formIn :
    B.formIn.IsSymm := by
  intro x y
  apply FaithfulSMul.injective_algebraMap S R
  simpa using B.symm.eq x y

@[simp]
lemma zero_lt_apply_root_root_iff'
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i))
    (hj : P.root j ∈ span S (range P.root) := subset_span (mem_range_self j)) :
    0 < B.formIn ⟨P.root i, hi⟩ ⟨P.root j, hj⟩ ↔ 0 < P.pairingIn S i j := by
  let ri : span S (range P.root) := ⟨P.root i, hi⟩
  let rj : span S (range P.root) := ⟨P.root j, hj⟩
  have : 2 * B.formIn ri rj = P.pairingIn S i j * B.formIn rj rj := by
    apply FaithfulSMul.injective_algebraMap S R
    simpa [map_ofNat] using P.two_mul_apply_root_root B i j
  calc 0 < B.formIn ri rj
      ↔ 0 < 2 * B.formIn ri rj := by rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.formIn rj rj := by rw [this]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_formIn_apply_root j)]

@[simp]
lemma zero_lt_apply_root_root_iff :
    (∃ s > 0, algebraMap S R s = B.form (P.root i) (P.root j)) ↔ 0 < P.pairingIn S i j := by
  rw [← zero_lt_apply_root_root_iff' B, B.zero_lt_formIn_iff]

include B

lemma zero_lt_pairing_iff :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i := by
  rw [← zero_lt_apply_root_root_iff' B, ← B.isSymm_formIn.eq, RingHom.id_apply,
    zero_lt_apply_root_root_iff']

lemma coxeterWeight_non_neg : 0 ≤ P.coxeterWeightIn S i j := by
  dsimp [coxeterWeightIn]
  by_cases h : 0 < P.pairingIn S i j
  · exact le_of_lt <| mul_pos h ((zero_lt_pairing_iff B i j).mp h)
  · have hn : ¬ 0 < P.pairingIn S j i := fun hc ↦ h ((zero_lt_pairing_iff B i j).mpr hc)
    simp_all only [not_lt, ge_iff_le]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

variable [NoZeroDivisors R]

omit [Module S M] [IsScalarTower S R M]

@[simp]
lemma apply_root_root_zero_iff :
    B.form (P.root i) (P.root j) = 0 ↔ P.pairing i j = 0 := by
  have _i := Algebra.charZero_of_charZero S R
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [two_mul_apply_root_root B i j]
    _ ↔ P.pairing i j = 0 := by simp [B.form_apply_root_ne_zero j]

lemma pairing_zero_iff :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  rw [← apply_root_root_zero_iff B, ← B.symm.eq, RingHom.id_apply, apply_root_root_zero_iff]

lemma coxeterWeight_zero_iff_isOrthogonal :
    P.coxeterWeight i j = 0 ↔ P.IsOrthogonal i j := by
  rw [coxeterWeight, mul_eq_zero]
  refine ⟨fun h => ?_, fun h => Or.inl h.1⟩
  rcases h with h | h
  · exact ⟨h, (pairing_zero_iff B i j).mp h⟩
  · exact ⟨(pairing_zero_iff B j i).mp h, h⟩

end RootPairing
