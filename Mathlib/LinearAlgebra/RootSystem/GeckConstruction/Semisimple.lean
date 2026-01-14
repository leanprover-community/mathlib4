/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# Geck's construction of a Lie algebra associated to a root system yields semisimple algebras

This file contains a proof that `RootPairing.GeckConstruction.lieAlgebra` yields semisimple Lie
algebras.

## Main definitions:

* `RootPairing.GeckConstruction.trace_toEnd_eq_zero`: the Geck construction yields trace-free
  matrices.

-/

noncomputable section

namespace RootPairing.GeckConstruction

open Function Module.End
open Set hiding diagonal
open scoped Matrix

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
  [Fintype ι] [DecidableEq ι] (i : b.support)

/-- An auxiliary lemma en route to `RootPairing.GeckConstruction.isNilpotent_e`. -/
private lemma isNilpotent_e_aux {j : ι} (n : ℕ) (h : letI _i := P.indexNeg; j ≠ -i) :
    (e i ^ n).col (.inr j) = 0 ∨
      ∃ (k : ι) (x : ℕ), P.root k = P.root j + n • P.root i ∧
        (e i ^ n).col (.inr j) = x • Pi.single (.inr k) 1 := by
  have _i : NoZeroSMulDivisors ℤ M := by have := P.reflexive_left; exact .int_of_charZero R M
  letI _i := P.indexNeg
  have aux (n : ℕ) : (e i ^ (n + 1)).col (.inr j) = (e i).mulVec ((e i ^ n).col (.inr j)) := by
    rw [pow_succ', ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]; simp
  induction n with
  | zero => exact Or.inr ⟨j, 1, by simp, by ext; simp [Pi.single_apply]⟩
  | succ n ih =>
    rcases ih with hn | ⟨k, x, hk₁, hk₂⟩
    · left; simp [aux, hn]
    rw [aux, hk₂, Matrix.mulVec_smul]
    have hki : k ≠ -i := by
      rintro rfl
      replace hk₁ : P.root (-j) = (n + 1) • P.root i := by
        simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self, neg_eq_iff_add_eq_zero,
          add_smul, one_smul] at hk₁ ⊢
        rw [← hk₁]
        module
      rcases n.eq_zero_or_pos with rfl | hn
      · apply h
        rw [zero_add, one_smul, EmbeddingLike.apply_eq_iff_eq] at hk₁
        simp [← hk₁, -indexNeg_neg]
      · have _i : (n + 1).AtLeastTwo := ⟨by omega⟩
        exact P.nsmul_notMem_range_root (n := n + 1) (i := i) ⟨-j, hk₁⟩
    by_cases hij : P.root j + (n + 1) • P.root i ∈ range P.root
    · obtain ⟨l, hl⟩ := hij
      right
      refine ⟨l, x * (P.chainBotCoeff i k + 1), hl, ?_⟩
      ext (m | m)
      · simp [e, -indexNeg_neg, hki]
      · rcases eq_or_ne m l with rfl | hml
        · replace hl : P.root m = P.root i + P.root k := by rw [hl, hk₁]; module
          simp [e, -indexNeg_neg, hl, mul_add]
        · replace hl : P.root m ≠ P.root i + P.root k :=
            fun contra ↦ hml (P.root.injective <| by rw [hl, contra, hk₁]; module)
          simp [e, -indexNeg_neg, hml, hl]
    · left
      ext (l | l)
      · simp [e, -indexNeg_neg, hki]
      · replace hij : P.root l ≠ P.root i + P.root k :=
          fun contra ↦ hij ⟨l, by rw [contra, hk₁]; module⟩
        simp [e, -indexNeg_neg, hij]

lemma isNilpotent_e :
    IsNilpotent (e i) := by
  classical
  have _i : NoZeroSMulDivisors ℤ M := by have := P.reflexive_left; exact .int_of_charZero R M
  letI _i := P.indexNeg
  rw [Matrix.isNilpotent_iff_forall_col]
  have case_inl (j : b.support) : (e i ^ 2).col (Sum.inl j) = 0 := by
    ext (k | k)
    · simp [e, sq, ne_neg P i, -indexNeg_neg]
    · have aux : ∀ x : ι, x ∈ Finset.univ → ¬ (x = i ∧ P.root k = P.root i + P.root x) := by
        suffices P.root k ≠ (2 : ℕ) • P.root i by simpa [two_smul]
        exact fun contra ↦ P.nsmul_notMem_range_root (n := 2) (i := i) ⟨k, contra⟩
      simp [e, sq, -indexNeg_neg, ← ite_and, Finset.sum_ite_of_false aux]
  rintro (j | j)
  · exact ⟨2, case_inl j⟩
  · by_cases hij : j = -i
    · use 2 + 1
      replace hij : (e i).col (Sum.inr j) = Pi.single (Sum.inl i) 1 := by
        ext (k | k)
        · simp [e, -indexNeg_neg, Pi.single_apply, hij]
        · have hk : P.root k ≠ P.root i + P.root j := by simp [hij, P.ne_zero k]
          simp [e, -indexNeg_neg, hk]
      rw [pow_succ, ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]
      simp [hij, case_inl i]
    use P.chainTopCoeff i j + 1
    rcases isNilpotent_e_aux i (P.chainTopCoeff i j + 1) hij with this | ⟨k, x, hk₁, -⟩
    · assumption
    exfalso
    replace hk₁ : P.root j + (P.chainTopCoeff i j + 1) • P.root i ∈ range P.root := ⟨k, hk₁⟩
    have hij' : LinearIndependent R ![P.root i, P.root j] := by
      apply IsReduced.linearIndependent P ?_ ?_
      · rintro rfl
        apply P.nsmul_notMem_range_root (n := P.chainTopCoeff i i + 2) (i := i)
        convert hk₁ using 1
        module
      · contrapose! hij
        rw [root_eq_neg_iff] at hij
        rw [hij, ← indexNeg_neg, neg_neg]
    rw [root_add_nsmul_mem_range_iff_le_chainTopCoeff hij'] at hk₁
    omega

lemma isNilpotent_f :
    IsNilpotent (f i) := by
  obtain ⟨n, hn⟩ := isNilpotent_e i
  suffices (ω b) * (f i ^ n) = 0 from ⟨n, by simpa [← mul_assoc] using congr_arg (ω b * ·) this⟩
  suffices (ω b) * (f i ^ n) = (e i ^ n) * (ω b) by simp [this, hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, ω_mul_f, ← mul_assoc]

omit [P.IsReduced] [IsDomain R] in
@[simp] lemma trace_h_eq_zero :
    (h i).trace = 0 := by
  letI _i := P.indexNeg
  suffices ∑ j, P.pairingIn ℤ j i = 0 by
    simp only [h_eq_diagonal, Matrix.trace_diagonal, Fintype.sum_sum_type, Finset.univ_eq_attach,
      Sum.elim_inl, Pi.zero_apply, Finset.sum_const_zero, Sum.elim_inr, zero_add]
    norm_cast
  suffices ∑ j, P.pairingIn ℤ (-j) i = ∑ j, P.pairingIn ℤ j i from
    eq_zero_of_neg_eq <| by simpa using this
  let σ : ι ≃ ι := Function.Involutive.toPerm _ neg_involutive
  exact σ.sum_comp (P.pairingIn ℤ · i)

open LinearMap LieModule in
/-- This is the main result of lemma 4.1 from [Geck](Geck2017). -/
lemma trace_toEnd_eq_zero (x : lieAlgebra b) :
    trace R _ (toEnd R _ (b.support ⊕ ι → R) x) = 0 := by
  obtain ⟨x, hx⟩ := x
  suffices trace R _ x.toLin' = 0 by simpa
  refine LieAlgebra.trace_toEnd_eq_zero ?_ hx
  rintro - ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · simp
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_e i)
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_f i)

end RootPairing.GeckConstruction
