/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

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
 * `RootPairing.pairing_zero_iff`: symmetric vanishing condition for `RootPairing.pairing`
 * `RootPairing.coxeterWeight_nonneg`: All pairs of roots have non-negative Coxeter weight.
 * `RootPairing.coxeterWeight_zero_iff_isOrthogonal` : A Coxeter weight vanishes iff the roots are
   orthogonal.

-/

noncomputable section

open Function Set Submodule

variable {ι R S M N : Type*} [LinearOrderedCommRing S] [CommRing R] [Algebra S R]
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
lemma apply_weylGroup_smul (g : P.weylGroup) (x y : M) :
    B.form (g • x) (g • y) = B.form x y := by
  revert x y
  obtain ⟨g, hg⟩ := g
  induction hg using weylGroup.induction with
  | mem i => simp
  | one => simp
  | mul g₁ g₂ hg₁ hg₂ hg₁' hg₂' =>
    intro x y
    rw [← Submonoid.mk_mul_mk _ _ _ hg₁ hg₂, mul_smul, mul_smul, hg₁', hg₂']

variable [NoZeroDivisors R] [NeZero (2 : R)]

@[simp]
lemma apply_root_root_zero_iff :
    B.form (P.root i) (P.root j) = 0 ↔ P.pairing i j = 0 := by
  calc B.form (P.root i) (P.root j) = 0
      ↔ 2 * B.form (P.root i) (P.root j) = 0 := by simp [two_ne_zero]
    _ ↔ P.pairing i j * B.form (P.root j) (P.root j) = 0 := by rw [B.two_mul_apply_root_root i j]
    _ ↔ P.pairing i j = 0 := by simp [B.ne_zero j]

include B

lemma pairing_zero_iff :
    P.pairing i j = 0 ↔ P.pairing j i = 0 := by
  rw [← B.apply_root_root_zero_iff, ← B.apply_root_root_zero_iff, ← B.symm.eq, RingHom.id_apply]

lemma coxeterWeight_zero_iff_isOrthogonal :
    P.coxeterWeight i j = 0 ↔ P.IsOrthogonal i j := by
  simp [coxeterWeight, IsOrthogonal, B.pairing_zero_iff i j]

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
  LinearMap.restrictScalarsRange (span S (range P.root)).subtype (span S (range P.root)).subtype
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
    B.posForm.IsSymm := by
  intro x y
  apply FaithfulSMul.algebraMap_injective S R
  simpa using B.symm.eq x y

lemma two_mul_posForm_apply_root_root :
    2 * B.posForm (P.rootSpanMem S i) (P.rootSpanMem S j) =
      P.pairingIn S i j * B.posForm (P.rootSpanMem S j) (P.rootSpanMem S j) := by
    apply FaithfulSMul.algebraMap_injective S R
    simpa [map_ofNat] using B.toInvariantForm.two_mul_apply_root_root i j

@[simp]
lemma zero_lt_apply_root_root_iff :
    0 < B.posForm (P.rootSpanMem S i) (P.rootSpanMem S j) ↔ 0 < P.pairingIn S i j := by
  calc  0 < B.posForm (P.rootSpanMem S i) (P.rootSpanMem S j)
      ↔ 0 < 2 * B.posForm (P.rootSpanMem S i) (P.rootSpanMem S j) := by
          rw [mul_pos_iff_of_pos_left zero_lt_two]
    _ ↔ 0 < P.pairingIn S i j * B.posForm (P.rootSpanMem S j) (P.rootSpanMem S j) := by
          rw [two_mul_posForm_apply_root_root]
    _ ↔ 0 < P.pairingIn S i j := by rw [mul_pos_iff_of_pos_right (B.zero_lt_posForm_apply_root j)]

end RootPositiveForm

include B

lemma zero_lt_pairingIn_iff :
    0 < P.pairingIn S i j ↔ 0 < P.pairingIn S j i := by
  rw [← B.zero_lt_apply_root_root_iff, ← B.isSymm_posForm.eq, RingHom.id_apply,
    B.zero_lt_apply_root_root_iff]

lemma coxeterWeight_nonneg : 0 ≤ P.coxeterWeightIn S i j := by
  dsimp [coxeterWeightIn]
  rcases lt_or_le 0 (P.pairingIn S i j) with h | h
  · exact le_of_lt <| mul_pos h ((zero_lt_pairingIn_iff B i j).mp h)
  · have hn : P.pairingIn S j i ≤ 0 := by rwa [← not_lt, ← zero_lt_pairingIn_iff B i j, not_lt]
    exact mul_nonneg_of_nonpos_of_nonpos h hn

section ultraparallel
/-! We consider the case `4 < P.coxeterWeight i j`.  A pair of roots with this configuration
are called `ultraparallel` in the literature.  The reflections in ultraparallel roots generate an
infinite dihedral group, so in particular, any root system with an ultraparallel pair is infinite.

Hmm. If I wait until we do polarization, then it suffices to construct a combination of roots with
nonpositive norm.
-/

variable (P : RootPairing ι R M N) [P.IsValuedIn S] (B : P.RootPositiveForm S) (i j : ι)

/-- This is a function that describes the coefficients attached to `P.root i` and `P.root j` of the
roots given by `(P.reflection i) ∘ (P.reflection j) (P.root i)`. -/
private def refl_coeff : ℕ → R × R
  | .zero => (1,0)
  | n + 1 => (((refl_coeff n).1 + (refl_coeff n).2) * P.coxeterWeight i j - (refl_coeff n).1,
    -(refl_coeff n).1 - (refl_coeff n).2)

omit [LinearOrderedCommRing S] [Algebra S R] B [FaithfulSMul S R]
 [P.IsValuedIn S] in
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

omit [LinearOrderedCommRing S] [Algebra S R] B [FaithfulSMul S R]
[P.IsValuedIn S] in
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

omit B [FaithfulSMul S R] [Module S M] [IsScalarTower S R M] in
lemma root_reflection_pos_coeff_left {a b : S} (ha : 0 < a) (hab : -2 * b < a)
    (hc : 4 < P.coxeterWeightIn S i j) : a < ((a + b) * P.coxeterWeightIn S i j - a) := by
  have hapb : 2 * a < (a + b) * 4 := by linarith
  have habz : 0 < a + b := by linarith
  have hab4 : (a + b) * 4 < (a + b) * P.coxeterWeightIn S i j := (mul_lt_mul_left habz).mpr hc
  calc
    a = 2 * a - a := by ring
    2 * a - a < (a + b) * 4 - a := sub_lt_sub_right hapb a
    (a + b) * 4 - a < (a + b) * P.coxeterWeightIn S i j - a := sub_lt_sub_right hab4 a
/-!
lemma root_reflection_pos_coeff_right {a b : R} (hab : -2 * b < a) : -(a + b) < b := by
  linarith
-/
omit B [FaithfulSMul S R] [Module S M] [IsScalarTower S R M] in
lemma root_refl_pos_coeff_right_2 {a b : S} (ha : 0 < a) (hab : -2 * b < a)
    (hc : 4 < P.coxeterWeightIn S i j) :
    (-2 * -(a + b)) < ((a + b) * P.coxeterWeightIn S i j - a) := by
  have habz : 0 < a + b := by linarith
  have hab4 : (a + b) * 4 < (a + b) * P.coxeterWeightIn S i j := (mul_lt_mul_left habz).mpr hc
  calc
    (-2 * -(a + b)) = 2 * a + 2 * b := by ring
    2 * a + 2 * b < 3 * a + 4 * b := by linarith
    3 * a + 4 * b = ((a + b) * 4 - a) := by ring
    ((a + b) * 4 - a) < ((a + b) * P.coxeterWeightIn S i j - a) := by linarith

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

end RootPairing
