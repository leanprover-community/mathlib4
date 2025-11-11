/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Invariant and root-positive bilinear forms on root pairings

This file contains basic results on Weyl-invariant inner products for root systems and root data.
Given a root pairing we define a structure which contains a bilinear form together with axioms for
reflection-invariance, symmetry, and strict positivity on all roots.  We show that root-positive
forms display the same sign behavior as the canonical pairing between roots and coroots.

Root-positive forms show up naturally as the invariant forms for symmetrizable Kac-Moody Lie
algebras.  In the finite case, the canonical polarization yields a root-positive form that is
positive semi-definite on weight space and positive-definite on the span of roots.

## Main definitions / results:

* `RootPairing.InvariantForm`: an invariant bilinear form on a root pairing.
* `RootPairing.RootPositiveForm`: Given a root pairing this is a structure which contains a
  bilinear form together with axioms for reflection-invariance, symmetry, and strict positivity on
  all roots.
* `RootPairing.zero_lt_pairingIn_iff`: sign relations between `RootPairing.pairingIn` and a
  root-positive form.
* `RootPairing.pairing_eq_zero_iff`: symmetric vanishing condition for `RootPairing.pairing`
* `RootPairing.coxeterWeight_nonneg`: All pairs of roots have non-negative Coxeter weight.
* `RootPairing.coxeterWeight_zero_iff_isOrthogonal` : A Coxeter weight vanishes iff the roots are
  orthogonal.

-/

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R S M N : Type*} [CommRing S] [LinearOrder S]
  [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- Given a root pairing, this is an invariant symmetric bilinear form. -/
structure InvariantForm (P : RootPairing ι R M N) where
  /-- The bilinear form bundled inside an `InvariantForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  ne_zero (i : ι) : form (P.root i) (P.root i) ≠ 0
  isOrthogonal_reflection (i : ι) : form.IsOrthogonal (P.reflection i)

namespace InvariantForm

variable {P : RootPairing ι R M N} (B : P.InvariantForm) (i j : ι)

lemma apply_root_ne_zero : B.form (P.root i) ≠ 0 :=
  fun contra ↦ B.ne_zero i <| by simp [contra]

lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [two_mul, ← eq_sub_iff_add_eq]
  nth_rw 1 [← B.isOrthogonal_reflection j]
  rw [reflection_apply, reflection_apply_self, root_coroot'_eq_pairing, LinearMap.map_sub₂,
    LinearMap.map_smul₂, smul_eq_mul, LinearMap.map_neg, LinearMap.map_neg, mul_neg, neg_sub_neg]

lemma pairing_mul_eq_pairing_mul_swap :
    P.pairing j i * B.form (P.root i) (P.root i) =
    P.pairing i j * B.form (P.root j) (P.root j) := by
  rw [← B.two_mul_apply_root_root i j, ← B.two_mul_apply_root_root j i, ← B.symm.eq,
    RingHom.id_apply]

@[simp]
lemma apply_reflection_reflection (x y : M) :
    B.form (P.reflection i x) (P.reflection i y) = B.form x y :=
  B.isOrthogonal_reflection i x y

@[simp]
lemma apply_root_root_zero_iff [IsDomain R] [NeZero (2 : R)] :
    B.form (P.root i) (P.root j) = 0 ↔ P.pairing i j = 0 := by
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp [two_ne_zero]
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [B.two_mul_apply_root_root i j]
    _ ↔ P.pairing i j = 0 := by simp [B.ne_zero j]

end InvariantForm

variable (S) in
/-- Given a root pairing, this is an invariant symmetric bilinear form satisfying a positivity
condition. -/
structure RootPositiveForm (P : RootPairing ι R M N) [P.IsValuedIn S] where
  /-- The bilinear form bundled inside a `RootPositiveForm`. -/
  form : LinearMap.BilinForm R M
  symm : form.IsSymm
  isOrthogonal_reflection (i : ι) : form.IsOrthogonal (P.reflection i)
  exists_eq (i j : ι) : ∃ s, algebraMap S R s = form (P.root i) (P.root j)
  exists_pos_eq (i : ι) : ∃ s > 0, algebraMap S R s = form (P.root i) (P.root i)

variable {P : RootPairing ι R M N} [P.IsValuedIn S] (B : P.RootPositiveForm S) (i j : ι)
  [FaithfulSMul S R] [Module S M] [IsScalarTower S R M]

namespace RootPositiveForm

omit [Module S M] [IsScalarTower S R M] in
lemma form_apply_root_ne_zero (i : ι) :
    B.form (P.root i) (P.root i) ≠ 0 := by
  obtain ⟨s, hs, hs'⟩ := B.exists_pos_eq i
  simpa [← hs'] using hs.ne'

/-- Forgetting the positivity condition, we may regard a `RootPositiveForm` as an `InvariantForm`.
-/
@[simps] def toInvariantForm : InvariantForm P where
  form := B.form
  symm := B.symm
  ne_zero := B.form_apply_root_ne_zero
  isOrthogonal_reflection := B.isOrthogonal_reflection

omit [Module S M] [IsScalarTower S R M] in
lemma two_mul_apply_root_root :
    2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.root j) :=
  B.toInvariantForm.two_mul_apply_root_root i j

/-- Given a root-positive form associated to a root pairing with coefficients in `R` but taking
values in `S`, this is the associated `S`-bilinear form on the `S`-span of the roots. -/
def posForm :
    LinearMap.BilinForm S (span S (range P.root)) :=
  LinearMap.restrictScalarsRange₂ (span S (range P.root)).subtype (span S (range P.root)).subtype
  (Algebra.linearMap S R) (FaithfulSMul.algebraMap_injective S R) B.form
  (fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ by
    apply LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (s := range P.root) (t := range P.root)
      (B := (LinearMap.restrictScalarsₗ S R _ _ _).comp (B.form.restrictScalars S))
    · rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
      simpa using B.exists_eq i j
    · simpa
    · simpa)

@[simp] lemma algebraMap_posForm {x y : span S (range P.root)} :
    algebraMap S R (B.posForm x y) = B.form x y := by
  change Algebra.linearMap S R _ = _
  simp [posForm]

lemma algebraMap_apply_eq_form_iff {x y : span S (range P.root)} {s : S} :
    algebraMap S R s = B.form x y ↔ s = B.posForm x y := by
  simp [RootPositiveForm.posForm]

lemma zero_lt_posForm_iff {x y : span S (range P.root)} :
    0 < B.posForm x y ↔ ∃ s > 0, algebraMap S R s = B.form x y := by
  refine ⟨fun h ↦ ⟨B.posForm x y, h, by simp⟩, fun ⟨s, h, h'⟩ ↦ ?_⟩
  rw [← B.algebraMap_posForm] at h'
  rwa [← FaithfulSMul.algebraMap_injective S R h']

lemma zero_lt_posForm_apply_root (i : ι)
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i)) :
    0 < B.posForm ⟨P.root i, hi⟩ ⟨P.root i, hi⟩ := by
  simpa only [zero_lt_posForm_iff] using B.exists_pos_eq i

lemma isSymm_posForm :
    B.posForm.IsSymm where
  eq x y := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa using B.symm.eq x y

/-- The length of the `i`-th root w.r.t. a root-positive form taking values in `S`. -/
def rootLength (i : ι) : S :=
  B.posForm (P.rootSpanMem S i) (P.rootSpanMem S i)

lemma rootLength_pos (i : ι) : 0 < B.rootLength i := by
  simpa using B.zero_lt_posForm_apply_root i

@[simp]
lemma rootLength_reflectionPerm_self (i : ι) :
    B.rootLength (P.reflectionPerm i i) = B.rootLength i := by
  simp [rootLength, rootSpanMem_reflectionPerm_self]

@[deprecated (since := "2025-05-28")]
alias rootLength_reflection_perm_self := rootLength_reflectionPerm_self

@[simp] lemma algebraMap_rootLength (i : ι) :
    algebraMap S R (B.rootLength i) = B.form (P.root i) (P.root i) := by
  simp [rootLength]

lemma pairingIn_mul_eq_pairingIn_mul_swap :
    P.pairingIn S j i * B.rootLength i = P.pairingIn S i j * B.rootLength j := by
  simpa only [← (algebraMap_injective S R).eq_iff, algebraMap_pairingIn, map_mul,
    B.algebraMap_rootLength] using B.toInvariantForm.pairing_mul_eq_pairing_mul_swap i j

@[simp]
lemma zero_lt_apply_root_root_iff [IsStrictOrderedRing S]
    (hi : P.root i ∈ span S (range P.root) := subset_span (mem_range_self i))
    (hj : P.root j ∈ span S (range P.root) := subset_span (mem_range_self j)) :
    0 < B.posForm ⟨P.root i, hi⟩ ⟨P.root j, hj⟩ ↔ 0 < P.pairingIn S i j := by
  let ri : span S (range P.root) := ⟨P.root i, hi⟩
  let rj : span S (range P.root) := ⟨P.root j, hj⟩
  have : 2 * B.posForm ri rj = P.pairingIn S i j * B.posForm rj rj := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa [map_ofNat] using B.toInvariantForm.two_mul_apply_root_root i j
  calc  0 < B.posForm ri rj
      ↔ 0 < 2 * B.posForm ri rj := by rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.posForm rj rj := by rw [this]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_posForm_apply_root j)]

end RootPositiveForm

include B

lemma zero_lt_pairingIn_iff [IsStrictOrderedRing S] :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i := by
  rw [← B.zero_lt_apply_root_root_iff, ← B.isSymm_posForm.eq, RingHom.id_apply,
    B.zero_lt_apply_root_root_iff]

lemma coxeterWeight_nonneg [IsStrictOrderedRing S] : 0 ≤ P.coxeterWeightIn S i j := by
  dsimp [coxeterWeightIn]
  rcases lt_or_ge 0 (P.pairingIn S i j) with h | h
  · exact le_of_lt <| mul_pos h ((zero_lt_pairingIn_iff B i j).mp h)
  · have hn : P.pairingIn S j i ≤ 0 := by rwa [← not_lt, ← zero_lt_pairingIn_iff B i j, not_lt]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

end RootPairing
