/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Sl2
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Lemmas

/-!
# Geck's construction of a Lie algebra associated to a root system

This file contains an implementation of Geck's construction of a semisimple Lie algebra from a
reduced crystallographic root system. It follows [Geck](Geck2017) quite closely.

## Main definitions:
* `RootPairing.GeckConstruction.lieAlgebra`: the Geck construction of the Lie algebra associated to
  a root system with distinguished base.
* `RootPairing.GeckConstruction.cartanSubalgebra`: a distinguished subalgebra corresponding to a
  Cartan subalgebra of the Geck construction.
* `RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra`: the distinguished subalgebra is
  contained in the Geck construction.
* `RootPairing.GeckConstruction.isSl2Triple`: a distinguished family of `sl₂` triples contained in
  the Geck construction.

## Alternative approaches

The are at least three ways to construct a Lie algebra from a root system:
1. As a quotient of a free Lie algebra, using the Serre relations
2. Directly defining the Lie bracket on $H ⊕ K^∣Φ|$
3. The Geck construction

We comment on these as follows:
1. This construction takes just a matrix as input. It yields a semisimple Lie algebra iff the
   matrix is a Cartan matrix but it is quite a lot of work to prove this. On the other hand, it also
   allows construction of Kac-Moody Lie algebras. It has been implemented as `Matrix.ToLieAlgebra`
   but as of May 2025, almost nothing has been proved about it in Mathlib.
2. This construction takes a root system with base as input, together with sufficient additional
   data to determine a collection of extraspecial pairs of roots. The additional data for the
   extraspecial pairs is required to pin down certain signs when defining the Lie bracket. (These
   signs can be interpreted as a set-theoretic splitting of Tits's extension of the Weyl group by
   an elementary 2-group of order $2^l$ where $l$ is the rank.)
3. This construction takes a root system with base as input and is implemented here.

There seems to be no known construction of a Lie algebra from a root system without first choosing
a base: https://mathoverflow.net/questions/495434/

## TODO
* Lemma stating `LinearIndependent R h` (easy using `RootPairing.Base.cartanMatrix_nondegenerate`).
* Instance stating `LieModule.IsIrreducible R (lieAlgebra b) (b.support ⊕ ι → R)`
  (Lemma 4.2 from [Geck](Geck2017)). This will immediately yield that the Geck construction is
  semisimple via `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful`.
* Instance stating `((cartanSubalgebra b).comap (lieAlgebra b).incl).IsCartanSubalgebra`
  (included in Lemma 4.6 from [Geck](Geck2017)).

-/

noncomputable section

open Set

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsCrystallographic] {b : P.Base}

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = - i then 1 else 0)
    (.of fun i' j ↦ if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j ↦ if i' = - i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))

variable (b)

/-- An involutive matrix which can transfer results between `RootPairing.GeckConstruction.e` and
`RootPairing.GeckConstruction.f`. -/
def ω :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 1 0 0 <| .of fun i j ↦ if i = -j then 1 else 0

/-- Geck's construction of the Lie algebra associated to a root system with distinguished base. -/
def lieAlgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range e ∪ range f)

/-- A distinguished subalgebra corresponding to a Cartan subalgebra of the Geck construction. -/
def cartanSubalgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range h)

variable {b}

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
lemma ω_mul_ω [DecidableEq ι] [Fintype ι] :
    ω b * ω b = 1 := by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in
lemma ω_mul_h [Fintype ι] (i : b.support) :
    ω b * h i = - h i * ω b := by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

lemma ω_mul_e [Fintype ι] (i : b.support) :
    ω b * e i = f i * ω b := by
  letI := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
    simp [← ite_and, and_comm, - indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

lemma ω_mul_f [Fintype ι] (i : b.support) :
    ω b * f i = e i * ω b := by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

lemma lie_e_f_mul_ω [Fintype ι] (i j : b.support) :
    ⁅e i, f j⁆ * ω b = - ω b * ⁅e j, f i⁆ := by
  classical
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def, mul_sub, neg_mul, neg_mul, sub_neg_eq_add]
  abel

variable [Fintype ι] (i j : b.support)

omit [Finite ι] [IsDomain R] [CharZero R] in
lemma lie_h_h :
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
lemma lie_h_e :
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
      Base.cartanMatrix, Base.cartanMatrixIn_def]
    refine ite_congr rfl (fun hkil ↦ ?_) (fun _ ↦ rfl)
    simp only [pairingIn_eq_add_of_root_eq_add hkil, Int.cast_add]
    ring

/-- Lemma 3.3 (b) from [Geck](Geck2017). -/
lemma lie_h_f :
    ⁅h j, f i⁆ = -b.cartanMatrix i j • f i := by
  classical
  suffices ω b * ⁅h j, f i⁆ = ω b * (-b.cartanMatrix i j • f i) by
    replace this := congr_arg (ω b * ·) this
    simpa [← mul_assoc, ω_mul_ω] using this
  calc ω b * ⁅h j, f i⁆ = ω b * (h j * f i - f i * h j) := by rw [Ring.lie_def]
                      _ = - (h j * e i - e i * h j) * ω b := ?_
                      _ = - ⁅h j, e i⁆ * ω b := by rw [Ring.lie_def]
                      _ = - (b.cartanMatrix i j • e i) * ω b := by rw [lie_h_e]
                      _ = ω b * (-b.cartanMatrix i j • f i) := ?_
  · rw [mul_sub, ← mul_assoc, ← mul_assoc, ω_mul_h, ω_mul_f, mul_assoc, mul_assoc, ω_mul_f, ω_mul_h,
      neg_sub, neg_mul, neg_mul, mul_neg, sub_mul, mul_assoc, mul_assoc]
    abel
  · rw [Matrix.mul_smul, ω_mul_f]
    simp [mul_assoc]

variable [P.IsReduced]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_same`. -/
private lemma lie_e_f_same_aux (k : ι) (hki : k ≠ i) (hki' : k ≠ P.reflectionPerm i i) :
    ⁅e i, f i⁆ (Sum.inr k) (Sum.inr k) = h i (Sum.inr k) (Sum.inr k) := by
  classical
  have h_lin_ind : LinearIndependent R ![P.root i, P.root k] := by
    rw [LinearIndependent.pair_symm_iff, IsReduced.linearIndependent_iff]; aesop
  suffices  (∑ x, if P.root k = P.root i + P.root x then
              (P.chainBotCoeff i x + 1 : R) * (P.chainTopCoeff i k + 1) else 0) -
            (∑ x, if P.root k = P.root x - P.root i then
              (P.chainTopCoeff i x + 1 : R) * (P.chainBotCoeff i k + 1) else 0) =
      P.chainBotCoeff i k - P.chainTopCoeff i k by
    have aux (x : ι) : P.root x = P.root k - P.root i ↔ P.root k = P.root i + P.root x := by
      rw [eq_sub_iff_add_eq', eq_comm]
    have aux' (x : ι) : P.root x = P.root i + P.root k ↔ P.root k = P.root x - P.root i := by
      rw [eq_sub_iff_add_eq', eq_comm]
    simpa [e, f, h, hki, hki', aux, aux', ← ite_and, ← P.chainBotCoeff_sub_chainTopCoeff h_lin_ind]
  rcases exists_or_forall_not (fun x ↦ P.root k = P.root i + P.root x) with ⟨x, hx⟩ | h₁ <;>
  rcases exists_or_forall_not (fun x ↦ P.root k = P.root x - P.root i) with ⟨y, hy⟩ | h₂
  · have h_lin_ind_x : LinearIndependent R ![P.root i, P.root x] := by simpa [hx] using h_lin_ind
    have h_lin_ind_y : LinearIndependent R ![P.root i, P.root y] := by
      rw [← add_eq_of_eq_sub hy, add_comm]; simpa
    have hx' : P.chainBotCoeff i k = P.chainBotCoeff i x + 1 :=
      chainBotCoeff_of_add h_lin_ind_x (add_comm (P.root i) _ ▸ hx)
    have hy' : P.chainTopCoeff i k = P.chainTopCoeff i y + 1 := chainTopCoeff_of_sub h_lin_ind_y hy
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (by aesop),
      Finset.sum_eq_single_of_mem y (Finset.mem_univ _) (by aesop)]
    simp only [hx, hy.symm, hx', hy', reduceIte, Nat.cast_add]
    ring
  · simp_rw [if_neg (h₂ _), Finset.sum_const_zero, sub_zero]
    replace h₂ : P.chainTopCoeff i k = 0 :=
      P.chainTopCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₂ x <| by simp [hx]
    have h_lin_ind_x : LinearIndependent R ![P.root i, P.root x] := by simpa [hx] using h_lin_ind
    have hx' : P.chainBotCoeff i k = P.chainBotCoeff i x + 1 :=
      chainBotCoeff_of_add h_lin_ind_x (add_comm (P.root i) _ ▸ hx)
    simp [hx, hx', h₂]
  · simp_rw [if_neg (h₁ _), Finset.sum_const_zero, zero_sub]
    replace h₁ : P.chainBotCoeff i k = 0 :=
      P.chainBotCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₁ x <| by simp [hx]
    have h_lin_ind_y : LinearIndependent R ![P.root i, P.root y] := by
      rw [← add_eq_of_eq_sub hy, add_comm]; simpa
    have hy' : P.chainTopCoeff i k = P.chainTopCoeff i y + 1 := chainTopCoeff_of_sub h_lin_ind_y hy
    simp [hy, hy', h₁]
  · suffices P.chainBotCoeff i k = 0 ∧ P.chainTopCoeff i k = 0 by simp [h₁, h₂, this]
    exact ⟨P.chainBotCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₁ x <| by simp [hx],
           P.chainTopCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₂ x <| by simp [hx]⟩

/-- Lemma 3.4 from [Geck](Geck2017). -/
lemma lie_e_f_same :
    ⁅e i, f i⁆ = h i := by
  letI _i := P.indexNeg
  have _i : NoZeroSMulDivisors ℤ M := have := P.reflexive_left; .int_of_charZero R M
  classical
  ext (k | k) (l | l)
  · simp [e, f, h]
  · have h₁ (x : ι) : ¬ (P.root x = P.root l - P.root i ∧ k = i ∧ x = -i) := by
      simp only [not_and]
      rintro contra rfl rfl
      simp [P.ne_zero, sub_eq_add_neg] at contra
    have h₂ (x : ι) : ¬ (P.root x = P.root i + P.root l ∧ k = i ∧ x = i) := by
      simp only [not_and]
      rintro contra rfl rfl
      simp [P.ne_zero] at contra
    simp [e, f, h, h₁, h₂, - indexNeg_neg, ← ite_and]
  · simp [e, f, h]
  · rcases eq_or_ne k i with rfl | hki
    · have hx (x : ι) : ¬ (P.root x = P.root i + P.root l ∧ P.root i = P.root x - P.root i) := by
        rintro ⟨-, contra⟩
        refine P.nsmul_notMem_range_root (n := 2) (i := i) ⟨x, ?_⟩
        rwa [eq_sub_iff_add_eq, ← two_smul ℕ, eq_comm] at contra
      simp only [e, f, h, P.ne_zero, P.ne_neg, Ring.lie_def, Fintype.sum_sum_type, Matrix.sub_apply,
        Matrix.mul_apply, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
        left_eq_add, zero_mul, mul_zero, ite_mul, mul_ite, ← ite_and]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
      simp [hx, eq_comm]
    rcases eq_or_ne k (-i) with rfl | hki'
    · have hx (x : ι) : ¬ (P.root x = P.root l - P.root i ∧ P.root (-i) = P.root i + P.root x) := by
        rintro ⟨-, contra⟩
        refine P.nsmul_notMem_range_root (n := 2) (i := -i) ⟨x, ?_⟩
        replace contra : P.root x = -(P.root i + P.root i) := by
          simpa [neg_eq_iff_add_eq_zero, ← add_assoc, add_eq_zero_iff_eq_neg'] using contra
        simp [contra, two_smul]
      have aux (x : ι) : ¬ P.root (-i) = P.root x - P.root i := by
        simp [P.ne_zero x, eq_comm]
      simp only [e, f, h, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.of_apply, hki, reduceIte, zero_mul, Finset.sum_const_zero,
        Matrix.fromBlocks_apply₂₂, mul_ite, ite_mul, mul_zero, ← ite_and, if_neg (hx _), add_zero,
        aux, zero_sub, Matrix.diagonal_apply]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
      simp [eq_comm, apply_ite ((- ·) : R → R)]
    rcases eq_or_ne k l with rfl | hkl
    · exact lie_e_f_same_aux i k hki hki'
    · simp_all [h, e, f]

lemma isSl2Triple [DecidableEq ι] :
    IsSl2Triple (h i) (e i) (f i) where
  h_ne_zero := fun contra ↦ by simpa [h] using congr_fun₂ contra (.inr i) (.inr i)
  lie_e_f := by rw [lie_e_f_same]
  lie_h_e_nsmul := by rw [lie_h_e]; simp
  lie_h_f_nsmul := by rw [lie_h_f]; simp

lemma cartanSubalgebra_le_lieAlgebra [DecidableEq ι] :
    cartanSubalgebra b ≤ lieAlgebra b := by
  rw [cartanSubalgebra, lieAlgebra, LieSubalgebra.lieSpan_le]
  rintro - ⟨i, rfl⟩
  rw [← lie_e_f_same]
  apply LieSubalgebra.lie_mem <;>
  exact LieSubalgebra.subset_lieSpan <| by simp

section lie_e_f_ne

open scoped Matrix

variable {i j}
variable (hij : i ≠ j)
omit [P.IsReduced]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₀ (k : b.support) (l : ι) :
    ⁅e i, f j⁆ (Sum.inl k) (Sum.inr l) = 0 := by
  classical
  letI := P.indexNeg
  have aux₁ : ∀ x ∈ Finset.univ, ¬ (P.root x = P.root i + P.root l ∧ k = j ∧ x = j) := by
    rintro  x - ⟨hl, -, rfl⟩
    exact b.sub_notMem_range_root i.property j.property ⟨-l, by simp [hl]⟩
  have aux₂ : ∀ x ∈ Finset.univ, ¬ (P.root x = P.root l - P.root j ∧ k = i ∧ x = -i) := by
    rintro  x - ⟨hl, -, rfl⟩
    replace hl : P.root i = P.root j - P.root l := by simpa [neg_eq_iff_eq_neg] using hl
    exact b.sub_notMem_range_root i.property j.property ⟨-l, by simp [hl]⟩
  simp [e, f, -indexNeg_neg, ← ite_and, Finset.sum_ite_of_false aux₁, Finset.sum_ite_of_false aux₂]

include hij

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₁ :
    ⁅e i, f j⁆ᵀ (Sum.inr j) = 0 := by
  letI := P.indexNeg
  classical
  ext (k | k)
  · rw [Matrix.transpose_apply, lie_e_f_ne_aux₀, Pi.zero_apply]
  · suffices ((if k = i then ↑|b.cartanMatrix i j| else (0 : R)) -
        ∑ x, if P.root x = P.root i + P.root j ∧ P.root k = P.root x - P.root j then
          (P.chainTopCoeff j x : R) + 1 else 0) = 0 by
      have hij : (j : ι) ≠ -i := by simpa using b.root_ne_neg_of_ne j.property i.property (by aesop)
      have aux : ∀ x ∈ Finset.univ,
        x ≠ j → (if x = j ∧ k = i then ↑|b.cartanMatrix i x| else 0) = (0 : R) := by aesop
      simpa [e, f, P.ne_zero, hij, -indexNeg_neg, -Finset.univ_eq_attach, ← ite_and,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ _) aux]
    rcases eq_or_ne k i with rfl | hk; swap
    · rw [if_neg (by tauto), Finset.sum_ite_of_false (by aesop)]; simp
    by_cases hij_mem : P.root i + P.root j ∈ range P.root
    · obtain ⟨m, hm⟩ := hij_mem
      rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (by rintro x - hx; simp [← hm, hx]),
        b.abs_cartanMatrix_apply, Base.cartanMatrix, Base.cartanMatrixIn_def]
      have aux₁ := b.chainTopCoeff_eq_of_ne hij.symm
      have aux₂ := chainTopCoeff_of_add (b.linearIndependent_pair_of_ne hij.symm) hm
      norm_cast
      aesop
    · have aux : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root j ∧ P.root i = P.root x - P.root j) := by
        rintro x - ⟨hx, -⟩; exact hij_mem ⟨x, hx⟩
      simp [Finset.sum_ite_of_false aux, b.cartanMatrix_apply_eq_zero_iff hij, hij_mem]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₂ :
    letI := P.indexNeg
    ⁅e i, f j⁆ᵀ (Sum.inr (-i)) = 0 := by
  letI := P.indexNeg
  classical
  ext (k | k)
  · rw [Matrix.transpose_apply, lie_e_f_ne_aux₀, Pi.zero_apply]
  · have aux : ⁅e i, f j⁆ (.inr k) (.inr (-i)) = (⁅e i, f j⁆ * ω b) (.inr k) (.inr i) := by simp [ω]
    rw [Matrix.transpose_apply, aux, lie_e_f_mul_ω, ← (-ω b * ⁅e j, f i⁆).transpose_apply,
      Matrix.transpose_mul, Matrix.mul_apply', lie_e_f_ne_aux₁ hij.symm]
    simp

/-- Lemma 3.5 from [Geck](Geck2017).

Note that the assumption `[P.IsNotG2]` is redundant and can be dropped by addressing:
https://github.com/leanprover-community/mathlib4/blob/6a0a7c723bd4fdc5ca679048efb76eb2bf725b3e/Mathlib/LinearAlgebra/RootSystem/Chain.lean#L551
-/
lemma lie_e_f_ne [P.IsNotG2] :
    ⁅e i, f j⁆ = 0 := by
  letI := P.indexNeg
  classical
  ext (k | k) (l | l)
  · aesop (erase simp indexNeg_neg) (add simp [e, f, Matrix.mul_apply, mul_ite, ite_mul])
  · exact lie_e_f_ne_aux₀ k l
  · have aux₁ : P.root k ≠ P.root i - P.root j :=
      fun contra ↦ b.sub_notMem_range_root i.property j.property ⟨k, contra⟩
    simp [e, f, ← sub_eq_add_neg, if_neg aux₁]
  · /- Geck Case 1 (covered by the auxiliary lemmas above). -/
    rcases eq_or_ne l j with rfl | h₃
    · rw [← ⁅e i, f j⁆.transpose_apply, lie_e_f_ne_aux₁ hij, Pi.zero_apply, Matrix.zero_apply]
    rcases eq_or_ne l (-i) with rfl | h₄
    · rw [← ⁅e i, f j⁆.transpose_apply, lie_e_f_ne_aux₂ hij, Pi.zero_apply, Matrix.zero_apply]
    /- Geck Case 2.
    It's all just definition unfolding and case analysis: the only real content is the external
    lemma `chainBotCoeff_mul_chainTopCoeff`. -/
    suffices
      (∑ x, if P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x then
          ((P.chainBotCoeff i x : R) + 1) * (P.chainTopCoeff j l + 1) else 0) =
      (∑ x, if P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j then
          ((P.chainTopCoeff j x : R) + 1) * (P.chainBotCoeff i l + 1) else 0) by
      have h₁ : ∀ x ∈ Finset.univ, ¬ ((x = i ∧ l = -i) ∧ k = -j) := by
        rintro - - ⟨⟨-, contra⟩, -⟩; contradiction
      have h₂ : ∀ x ∈ Finset.univ, ¬ ((x = j ∧ l = j) ∧ k = i) := by
        rintro - - ⟨⟨-, contra⟩, -⟩; contradiction
      rw [← sub_eq_zero] at this
      simpa [e, f, ← ite_and, Finset.sum_ite_of_false h₁, Finset.sum_ite_of_false h₂, -indexNeg_neg,
        -Finset.univ_eq_attach]
    by_cases h₅ : P.root l + P.root i - P.root j ∈ range P.root; swap
    · have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, hx'⟩; exact h₅ ⟨k, by rw [hx', hx]; abel⟩
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact h₅ ⟨k, by rw [hx', hx]; abel⟩
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    by_cases h₆ : P.root l + P.root i ∈ range P.root; swap
    · have h₇ : P.root l - P.root j ∉ range P.root := by
        rwa [b.root_sub_mem_iff_root_add_mem i j l (by aesop) i.property j.property
          (by aesop) (by aesop) h₅]
      have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, -⟩; exact h₆ ⟨x, by rw [hx]; abel⟩
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact h₇ ⟨x, hx⟩
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    obtain ⟨m, hm : P.root m = P.root l - P.root j⟩ :=
      b.root_sub_root_mem_of_mem_of_mem i j l (by aesop) i.property j.property h₅ h₃ h₆
    obtain ⟨l', hl'⟩ := h₆
    by_cases hk : P.root k = P.root l + P.root i - P.root j; swap
    · grind
    have aux₃ (x) (hx : x ≠ m) :
      ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        grind [EmbeddingLike.apply_eq_iff_eq]
    have aux₄ (x) (hx : x ≠ l') :
      ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        grind [EmbeddingLike.apply_eq_iff_eq]
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (by rintro x - h; rw [if_neg (aux₃ _ h)]),
      Finset.sum_eq_single_of_mem l' (Finset.mem_univ _) (by rintro x - h; rw [if_neg (aux₄ _ h)]),
      if_pos (⟨hm, by rw [hm, hk]; abel⟩), if_pos ⟨by rw [hl', add_comm], by rw [hl', hk]⟩]
    have := chainBotCoeff_mul_chainTopCoeff i.property j.property (by aesop) hl'.symm hm.symm h₅
    norm_cast

end lie_e_f_ne

end RootPairing.GeckConstruction
