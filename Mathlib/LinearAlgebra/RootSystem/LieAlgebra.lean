/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# The Lie algebra of a root system

## TODO
* Lemma stating `LinearIndependent R b.h` (Uses `RootPairing.Base.cartanMatrix_nondegenerate`.)
* Lemma stating `⁅e i, f j⁆ = 0` when `i ≠ j` (Lemma 3.5 from [Geck](Geck2017).)

## Main definitions:
* `RootPairing.Base.lieAlgebra`: ...
* `RootPairing.Base.cartanSubalgebra`: ...

## Alternative approaches

Mention:
* Serre relations
* Chevalley / Tits: choose base, ordering, signs for extraspecial pairs. Mention "Tits section",
  extended Weyl group.
* Geck: NB does not give basis for Lie algebra
* Seems no approach that does not require choosing base

-/

noncomputable section

open Set

namespace RootPairing.Base

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsCrystallographic]
  {b : P.Base}

def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = - i then 1 else 0)
    (.of fun i' j ↦ if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j ↦ if i' = - i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))

def ω :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 1 0 0 <| .of fun i j ↦ if i = -j then 1 else 0

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
lemma ω_mul_ω [DecidableEq ι] [Fintype ι] [Fintype b.support] :
    b.ω * b.ω = 1 := by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

lemma ω_mul_e [DecidableEq ι] [Fintype ι] [Fintype b.support] (i : b.support) :
    b.ω * b.e i = b.f i * b.ω := by
  letI := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
    simp [← ite_and, and_comm, ← indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

lemma ω_mul_f [DecidableEq ι] [Fintype ι] [Fintype b.support] (i : b.support) :
    b.ω * b.f i = b.e i * b.ω := by
  have := congr_arg (· * ω) (congr_arg (ω * ·) (b.ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

omit [Finite ι] [IsDomain R] in
lemma ω_mul_h [DecidableEq ι] [Fintype ι] [Fintype b.support] (i : b.support) :
    b.ω * b.h i = - b.h i * b.ω := by
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

omit [Finite ι] [IsDomain R] [CharZero R] in
lemma lie_h_h [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h i, h j⁆ = 0 := by
  classical
  ext (k | k) (l | l)
  · simp [h]
  · simp [h]
  · simp [h]
  · simp only [h, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, ite_mul, mul_comm (P.pairingIn ℤ k i : R)]
    aesop

/-- Lemma 3.3 (a) from [Geck](Geck2017). -/
lemma lie_h_e [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h j, e i⁆ = b.cartanMatrix i j • e i := by
  classical
  ext (k | k) (l | l)
  · simp [h, e]
  · simp only [h, e, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, add_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_ite l (by aesop)]
    aesop
  · simp only [h, e]
    aesop
  · simp only [h, e, indexNeg_neg, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_self, Finset.sum_const_zero,
      Matrix.fromBlocks_apply₂₂, zero_add, ite_mul, zero_mul, Matrix.smul_apply, smul_ite, smul_add,
      zsmul_eq_mul, smul_zero]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ {k, l}) (by aesop)]
    rcases eq_or_ne k l with rfl | hkl; · simp [P.ne_zero i]
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Finset.mem_singleton, Finset.sum_singleton, Finset.sum_insert, hkl, not_false_eq_true,
      reduceIte, right_eq_add, ite_self, add_zero, zero_add, ite_sub_ite, sub_self,
      cartanMatrix, cartanMatrixIn_def]
    refine ite_congr rfl (fun hkil ↦ ?_) (fun _ ↦ rfl)
    simp only [pairingIn_eq_add_of_root_eq_add hkil, Int.cast_add]
    ring

/-- Lemma 3.3 (b) from [Geck](Geck2017). -/
lemma lie_h_f [Fintype b.support] [Fintype ι] (i j : b.support) :
    ⁅h j, f i⁆ = -b.cartanMatrix i j • f i := by
  classical
  suffices ω * ⁅h j, f i⁆ = ω * (-b.cartanMatrix i j • f i) by
    replace this := congr_arg (ω * ·) this
    simpa [← mul_assoc, ω_mul_ω] using this
  calc ω * ⁅h j, f i⁆ = ω * (h j * f i - f i * h j) := by rw [Ring.lie_def]
                    _ = - (h j * e i - e i * h j) * ω := ?_
                    _ = - ⁅h j, e i⁆ * ω := by rw [Ring.lie_def]
                    _ = - (b.cartanMatrix i j • e i) * ω := by rw [lie_h_e]
                    _ = ω * (-b.cartanMatrix i j • f i) := ?_
  · rw [mul_sub, ← mul_assoc, ← mul_assoc, ω_mul_h, ω_mul_f, mul_assoc, mul_assoc, ω_mul_f, ω_mul_h,
      neg_sub, neg_mul, neg_mul, mul_neg, sub_mul, mul_assoc, mul_assoc]
    abel
  · rw [Matrix.mul_smul, ω_mul_f]
    simp [mul_assoc]

/-- Lemma 3.4 from [Geck](Geck2017). -/
lemma lie_e_f_same [P.IsReduced] [Fintype b.support] [Fintype ι] (i : b.support) :
    ⁅e i, f i⁆ = h i := by
  letI := P.indexNeg
  have _i : NoZeroSMulDivisors ℤ M := have := P.reflexive_left; .int_of_charZero R M
  classical
  ext (k | k) (l | l)
  · simp [Ring.lie_def, e, f, h, Matrix.mul_apply]
  · simp [Ring.lie_def, e, f, h, Matrix.mul_apply, ← indexNeg_neg, sub_eq_zero]
    congr
    ext m
    rw [← ite_and, ← ite_and, if_neg, if_neg]
    · rintro ⟨contra, -, rfl⟩
      simp [P.ne_zero l] at contra
    · rintro ⟨contra, -, rfl⟩
      simp [P.ne_zero l, sub_eq_add_neg] at contra
  · simp [Ring.lie_def, e, f, h, Matrix.mul_apply]
  · simp [Ring.lie_def, e, f, h, Matrix.mul_apply, ← indexNeg_neg, Matrix.diagonal_apply,
      ← ite_and]
    rcases eq_or_ne k i with rfl | hki
    · simp [-indexNeg_neg, P.ne_zero, P.ne_neg]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
      have (x : ι) : ¬ (P.root x = P.root i + P.root l ∧ P.root ↑i = P.root x - P.root i) := by
        rintro ⟨h₁, h₂⟩
        have : i = l := by simpa [h₁] using h₂
        replace h₁ : P.root x = (2 : R) • P.root l := by rw [two_smul, h₁, this]
        exact P.two_smul_notMem_range_root ⟨x, h₁⟩
      simp_rw [if_neg (this _)]
      aesop
    simp [-indexNeg_neg, hki]
    rcases eq_or_ne k (-i) with rfl | hki'
    · simp [-indexNeg_neg, P.ne_zero, P.ne_neg]
      have aux₁ (x : ι) : ¬ P.root (-i) = P.root x - P.root i := by
        rw [eq_comm]
        simp [eq_sub_iff_add_eq, P.ne_zero x]
      simp [-indexNeg_neg, aux₁]
      have aux₂ (x : ι) :
          ¬ (P.root x = P.root l - P.root i ∧ P.root (-i) = P.root i + P.root x) := by
        rintro ⟨h₁, h₂⟩
        have : -i = l := by simpa [-indexNeg_neg, h₁] using h₂
        replace h₁ : P.root x = (2 : R) • P.root l := by
          rw [two_smul, h₁, this.symm, indexNeg_neg, root_reflection_perm, reflection_apply_self]
          abel
        exact P.two_smul_notMem_range_root ⟨x, h₁⟩
      simp_rw [if_neg (aux₂ _)]
      simp [-indexNeg_neg]
      rcases eq_or_ne l (-i) with rfl | hil
      · simp
      simp [-indexNeg_neg, hil, hil.symm]
    have h_lin_ind : LinearIndependent R ![P.root i, P.root k] := by
      rw [LinearIndependent.pair_symm_iff]
      simpa [IsReduced.linearIndependent_iff, hki] using hki'
    simp [-indexNeg_neg, hki', ← P.chainBotCoeff_sub_chainTopCoeff h_lin_ind]
    rcases eq_or_ne k l with rfl | hkl
    · simp [-indexNeg_neg]
      have aux (x : ι) : P.root x = P.root k - P.root i ↔ P.root k = P.root i + P.root x := by
        rw [eq_sub_iff_add_eq', eq_comm]
      simp only [aux, and_self]
      replace aux (x : ι) : P.root x = P.root i + P.root k ↔ P.root k = P.root x - P.root i := by
        rw [eq_sub_iff_add_eq', eq_comm]
      simp only [aux, and_self]
      -- This goal is essentially the only part with content. Separate lemma?
      rcases exists_or_forall_not (fun x ↦ P.root k = P.root i + P.root x) with h₁ | h₁ <;>
      rcases exists_or_forall_not (fun x ↦ P.root k = P.root x - P.root i) with h₂ | h₂
      · obtain ⟨x, hx⟩ := h₁
        obtain ⟨y, hy⟩ := h₂
        have h_lin_ind_x : LinearIndependent R ![P.root i, P.root x] := by
          simpa [hx] using h_lin_ind
        have h_lin_ind_y : LinearIndependent R ![P.root i, P.root y] := by
          rw [← add_eq_of_eq_sub hy, add_comm]; simpa
        have hx' : P.chainBotCoeff i k = P.chainBotCoeff i x + 1 := by
          rw [add_comm] at hx
          exact chainBotCoeff_of_add h_lin_ind_x hx
        have hy' : P.chainTopCoeff i k = P.chainTopCoeff i y + 1 :=
          chainTopCoeff_of_sub h_lin_ind_y hy
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (by aesop),
          Finset.sum_eq_single_of_mem y (Finset.mem_univ _) (by aesop)]
        simp [hx, hy.symm, hx', hy']
        ring
      · simp_rw [if_neg (h₂ _), Finset.sum_const_zero, sub_zero]
        replace h₂ : P.chainTopCoeff i k = 0 := by
          rw [chainTopCoeff_eq_zero_iff]
          right
          rintro ⟨m, hm⟩
          apply h₂ m
          simp [hm]
        obtain ⟨x, hx⟩ := h₁
        have h_lin_ind' : LinearIndependent R ![P.root i, P.root x] := by simpa [hx] using h_lin_ind
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (by aesop)]
        rw [add_comm] at hx
        rw [chainBotCoeff_of_add h_lin_ind' hx]
        rw [add_comm] at hx
        simp [hx, h₂]
      · simp_rw [if_neg (h₁ _), Finset.sum_const_zero, zero_sub]
        replace h₁ : P.chainBotCoeff i k = 0 := by
          rw [chainBotCoeff_eq_zero_iff]
          right
          rintro ⟨m, hm⟩
          apply h₁ m
          simp [hm]
        obtain ⟨x, hx⟩ := h₂
        have h_lin_ind' : LinearIndependent R ![P.root i, P.root x] := by
          rw [← add_eq_of_eq_sub hx, add_comm]; simpa
        rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (by aesop)]
        simp [hx, h₁, chainTopCoeff_of_sub h_lin_ind' hx]
      · suffices P.chainBotCoeff i k = 0 ∧ P.chainTopCoeff i k = 0 by
          simp [if_neg (h₁ _), if_neg (h₂ _), this]
        replace h₁ : P.root k - P.root i ∉ range P.root := by
          rintro ⟨x, hx⟩
          apply h₁ x
          simp [hx]
        replace h₂ : P.root k + P.root i ∉ range P.root := by
          rintro ⟨x, hx⟩
          apply h₂ x
          simp [hx]
        refine ⟨?_, ?_⟩
        · contrapose! h₁
          replace h₁ : 1 ≤ P.chainBotCoeff i k := by omega
          simpa [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h_lin_ind] using h₁
        · contrapose! h₂
          replace h₂ : 1 ≤ P.chainTopCoeff i k := by omega
          simpa [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h_lin_ind] using h₂
    have h₁ (x : ι) : ¬ (P.root x = P.root l - P.root i ∧ P.root k = P.root i + P.root x) := by
      rintro ⟨hx₁, hx₂⟩
      simp [hx₁, hkl] at hx₂
    have h₂ (x : ι) : ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root i) := by
      rintro ⟨hx₁, hx₂⟩
      simp [hx₁, hkl] at hx₂
    simp [if_neg (h₁ _), if_neg (h₂ _), hkl]

lemma isSl2Triple [P.IsReduced] [Fintype b.support] [Fintype ι] [DecidableEq ι] (i : b.support) :
    IsSl2Triple (h i) (e i) (f i) where
  h_ne_zero := fun contra ↦ by simpa [h] using congr_fun₂ contra (.inr i) (.inr i)
  lie_e_f := by rw [lie_e_f_same]
  lie_h_e_nsmul := by rw [lie_h_e]; simp
  lie_h_f_nsmul := by rw [lie_h_f]; simp

variable (b)
variable [Fintype b.support] [Fintype ι] [DecidableEq ι]

/-- The Lie algebra associated to a root system with distinguished base. -/
def lieAlgebra :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range e ∪ range f)

/-- The Cartan subalgebra of the Lie algebra associated to a root system with distinguished base. -/
def cartanSubalgebra :
    LieSubalgebra R b.lieAlgebra :=
  (LieSubalgebra.lieSpan R _ (range b.h)).comap (lieAlgebra b).incl

end RootPairing.Base
