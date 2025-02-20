/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Reduced root pairings

This file contains basic definitions and results related to reduced root pairings.

## Main definitions:

 * `RootPairing.IsReduced`: A root pairing is said to be reduced if two linearly dependent roots are
   always related by a sign.
 * `RootPairing.linInd_iff_coxeterWeight_ne_four`: for a finite root pairing, two
   roots are linearly independent iff their Coxeter weight is not four.

-/

open Module Set Function

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) {i j : ι}

namespace RootPairing

/-- A root pairing is said to be reduced if any linearly dependent pair of roots is related by a
sign. -/
def IsReduced : Prop :=
  ∀ i j, ¬ LinearIndependent R ![P.root i, P.root j] → (P.root i = P.root j ∨ P.root i = - P.root j)

lemma isReduced_iff : P.IsReduced ↔ ∀ i j : ι, i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · rcases eq_or_ne i j with rfl | h'
    · tauto
    · exact Or.inr (h i j h' hLin)

lemma infinite_of_linInd_coxeterWeight_four [NeZero (2 : R)] [NoZeroSMulDivisors ℤ M]
    (hl : LinearIndependent R ![P.root i, P.root j]) (hc : P.coxeterWeight i j = 4) :
    Infinite ι := by
  refine (infinite_range_iff (Embedding.injective P.root)).mp (Infinite.mono ?_
    ((infinite_range_reflection_reflection_iterate_iff (P.coroot_root_two i)
    (P.coroot_root_two j) ?_).mpr ?_))
  · rw [range_subset_iff]
    intro n
    rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo (P.coroot_root_two i)
      (P.mapsTo_reflection_root i)).comp (bijOn_reflection_of_mapsTo (P.coroot_root_two j)
      (P.mapsTo_reflection_root j))).image_eq n]
    exact mem_image_of_mem _ (mem_range_self j)
  · rw [coroot_root_eq_pairing, coroot_root_eq_pairing, ← hc, mul_comm, coxeterWeight]
  · rw [LinearIndependent.pair_iff] at hl
    specialize hl (P.pairing j i) (-2)
    simp only [neg_smul, neg_eq_zero, two_ne_zero (α := R), and_false, imp_false] at hl
    rw [ne_eq, coroot_root_eq_pairing, ← sub_eq_zero, sub_eq_add_neg]
    exact hl

lemma pairing_smul_root_eq_of_not_linInd [NeZero (2 : R)] [NoZeroSMulDivisors R M]
    (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.pairing j i • P.root i = (2 : R) • P.root j := by
  rw [LinearIndependent.pair_iff] at h
  push_neg at h
  obtain ⟨s, t, h₁, h₂⟩ := h
  replace h₂ : s ≠ 0 := by
    rcases eq_or_ne s 0 with rfl | hs
    · exact False.elim <| h₂ rfl <| (smul_eq_zero_iff_left <| P.ne_zero j).mp <| by simpa using h₁
    · assumption
  have h₃ : t ≠ 0 := by
    rcases eq_or_ne t 0 with rfl | ht
    · exact False.elim <| h₂ <| (smul_eq_zero_iff_left <| P.ne_zero i).mp <| by simpa using h₁
    · assumption
  replace h₁ : s • P.root i = -t • P.root j := by rwa [← eq_neg_iff_add_eq_zero, ← neg_smul] at h₁
  have h₄ : s * 2 = - (t * P.pairing j i) := by simpa using congr_arg (P.coroot' i) h₁
  replace h₁ : (2 : R) • (s • P.root i) = (2 : R) • (-t • P.root j) := by rw [h₁]
  rw [smul_smul, mul_comm, h₄, smul_comm, ← neg_mul, ← smul_smul] at h₁
  exact smul_right_injective M (neg_ne_zero.mpr h₃) h₁

section Finite

variable [Finite ι]

lemma coxeterWeight_ne_four_of_linearIndependent [NeZero (2 : R)] [NoZeroSMulDivisors ℤ M]
    (hl : LinearIndependent R ![P.root i, P.root j]) :
    P.coxeterWeight i j ≠ 4 := by
  intro contra
  have := P.infinite_of_linInd_coxeterWeight_four hl contra
  exact not_finite ι

variable [CharZero R] [NoZeroSMulDivisors R M]

lemma linearIndependent_iff_coxeterWeight_ne_four :
    LinearIndependent R ![P.root i, P.root j] ↔ P.coxeterWeight i j ≠ 4 := by
  have : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  refine ⟨coxeterWeight_ne_four_of_linearIndependent P, fun h ↦ ?_⟩
  contrapose! h
  have h₁ := P.pairing_smul_root_eq_of_not_linInd h
  rw [LinearIndependent.pair_symm_iff] at h
  have h₂ := P.pairing_smul_root_eq_of_not_linInd h
  suffices P.coxeterWeight i j • P.root i = (4 : R) • P.root i from
    smul_left_injective R (P.ne_zero i) this
  calc P.coxeterWeight i j • P.root i
      = (P.pairing i j * P.pairing j i) • P.root i := by rfl
    _ = P.pairing i j • (2 : R) • P.root j := by rw [mul_smul, h₁]
    _ = (4 : R) • P.root i := by rw [smul_comm, h₂, ← mul_smul]; norm_num

lemma coxeterWeight_eq_four_iff_not_linearIndependent :
    P.coxeterWeight i j = 4 ↔ ¬ LinearIndependent R ![P.root i, P.root j] := by
  rw [P.linearIndependent_iff_coxeterWeight_ne_four, not_not]

variable (i j)

@[simp]
lemma pairing_two_two_iff :
    P.pairing i j = 2 ∧ P.pairing j i = 2 ↔ i = j := by
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ by simp [h]⟩
  have : ¬ LinearIndependent R ![P.root i, P.root j] := by
    rw [← coxeterWeight_eq_four_iff_not_linearIndependent, coxeterWeight, h₁, h₂]; norm_num
  replace this := P.pairing_smul_root_eq_of_not_linInd this
  exact P.root.injective <| smul_right_injective M two_ne_zero (h₂ ▸ this)

@[simp]
lemma pairing_neg_two_neg_two_iff :
    P.pairing i j = -2 ∧ P.pairing j i = -2 ↔ P.root i = -P.root j := by
  simp only [← neg_eq_iff_eq_neg]
  simpa [eq_comm (a := -P.root i), root_eq_neg_iff] using
    P.pairing_two_two_iff i (P.reflection_perm j j)

variable [NoZeroSMulDivisors R N]

lemma pairing_one_four_iff' (h2 : IsSMulRegular R (2 : R)) :
    P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i := by
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  have _i : NoZeroSMulDivisors ℤ N := NoZeroSMulDivisors.int_of_charZero R N
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : ¬ LinearIndependent R ![P.root i, P.root j] := by
      rw [← coxeterWeight_eq_four_iff_not_linearIndependent, coxeterWeight, h₁, h₂]; norm_num
    replace this := P.pairing_smul_root_eq_of_not_linInd this
    rw [h₂, show (4 : R) = 2 * 2 by norm_num, mul_smul] at this
    exact smul_right_injective M two_ne_zero this.symm
  · rw [← coroot_eq_smul_coroot_iff] at h
    rw [pairing, pairing, h]
    norm_num
    suffices (2 : R) • P.pairing i j = (2 : R) • 1 from h2 this
    rw [pairing, ← map_smul, ← h]
    simp

lemma pairing_neg_one_neg_four_iff' (h2 : IsSMulRegular R (2 : R)) :
    P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i := by
  simpa [neg_smul, ← neg_eq_iff_eq_neg] using P.pairing_one_four_iff' i (P.reflection_perm j j) h2

@[simp]
lemma pairing_one_four_iff [NoZeroDivisors R] :
    P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i :=
  P.pairing_one_four_iff' i j <| smul_right_injective R two_ne_zero

@[simp]
lemma pairing_neg_one_neg_four_iff [NoZeroDivisors R] :
    P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i :=
  P.pairing_neg_one_neg_four_iff' i j <| smul_right_injective R two_ne_zero

end Finite

end RootPairing
