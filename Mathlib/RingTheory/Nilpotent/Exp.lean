/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Nat.Cast.Field
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.FieldSimp

/-!
# Exponential map on algebras

This file defines the exponential map `IsNilpotent.exp` on `ℚ`-algebras. The definition of
`IsNilpotent.exp a` applies to any element `a` in an algebra over `ℚ`, though it yields meaningful
(non-junk) values only when `a` is nilpotent.

The main result is `IsNilpotent.exp_add_of_commute`, which establishes the expected connection
between the additive and multiplicative structures of `A` for commuting nilpotent elements.

Additionally, `IsNilpotent.isUnit_exp` shows that if `a` is nilpotent in `A`, then
`IsNilpotent.exp a` is a unit in `A`.

Note: Although the definition works with `ℚ`-algebras, the results can be applied to any algebra
over a characteristic zero field.

## Main definitions

  * `IsNilpotent.exp`

## Tags

algebra, exponential map, nilpotent
-/

namespace IsNilpotent

variable {A : Type*} [Ring A] [Module ℚ A]

open Finset
open scoped Nat

/-- The exponential map on algebras, defined in analogy with the usual exponential series.
It provides meaningful (non-junk) values for nilpotent elements. -/
noncomputable def exp (a : A) : A :=
  ∑ i ∈ range (nilpotencyClass a), (i.factorial : ℚ)⁻¹ • (a ^ i)

theorem exp_eq_sum {a : A} {k : ℕ} (h : a ^ k = 0) :
    exp a = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) := by
  have h₁ : ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) =
      ∑ i ∈ range (nilpotencyClass a), (i.factorial : ℚ)⁻¹ • (a ^ i) +
        ∑ i ∈ Ico (nilpotencyClass a) k, (i.factorial : ℚ)⁻¹ • (a ^ i) :=
    (sum_range_add_sum_Ico _ (csInf_le' h)).symm
  suffices ∑ i ∈ Ico (nilpotencyClass a) k, (i.factorial : ℚ)⁻¹ • (a ^ i) = 0 by
    dsimp [exp]
    rw [h₁, this, add_zero]
  exact sum_eq_zero fun _ h₂ => by
    rw [pow_eq_zero_of_le (mem_Ico.1 h₂).1 (pow_nilpotencyClass ⟨k, h⟩), smul_zero]

theorem exp_smul_eq_sum {M : Type*} [AddCommGroup M] [Module A M] [Module ℚ M] {a : A} {m : M}
    {k : ℕ} (h : (a ^ k) • m = 0) (hn : IsNilpotent a) :
    exp a • m = ∑ i ∈ range k, (i.factorial : ℚ)⁻¹ • (a ^ i) • m := by
  rcases le_or_gt (nilpotencyClass a) k with h₀ | h₀
  · simp_rw [exp_eq_sum (pow_eq_zero_of_le h₀ (pow_nilpotencyClass hn)), sum_smul, smul_assoc]
  rw [exp, sum_smul, ← sum_range_add_sum_Ico _ (Nat.le_of_succ_le h₀)]
  suffices ∑ i ∈ Ico k (nilpotencyClass a), ((i.factorial : ℚ)⁻¹ • (a ^ i)) • m = 0 by
    simp_rw [this, add_zero, smul_assoc]
  refine sum_eq_zero fun r h₂ ↦ ?_
  rw [smul_assoc, ← pow_sub_mul_pow a (mem_Ico.1 h₂).1, mul_smul, h, smul_zero, smul_zero]

theorem exp_add_of_commute {a b : A} (h₁ : Commute a b) (h₂ : IsNilpotent a) (h₃ : IsNilpotent b) :
    exp (a + b) = exp a * exp b := by
  obtain ⟨n₁, hn₁⟩ := h₂
  obtain ⟨n₂, hn₂⟩ := h₃
  let N := n₁ ⊔ n₂
  have h₄ : a ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₁
  have h₅ : b ^ (N + 1) = 0 := pow_eq_zero_of_le (by omega) hn₂
  rw [exp_eq_sum (k := 2 * N + 1)
    (Commute.add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero h₁ h₄ h₅ (by cutsat)),
    exp_eq_sum h₄, exp_eq_sum h₅]
  set R2N := range (2 * N + 1) with hR2N
  set RN := range (N + 1) with hRN
  have s₁ := by
    calc ∑ i ∈ R2N, (i ! : ℚ)⁻¹ • (a + b) ^ i
        = ∑ i ∈ R2N, (i ! : ℚ)⁻¹ • ∑ j ∈ range (i + 1), a ^ j * b ^ (i - j) * i.choose j := ?_
      _ = ∑ i ∈ R2N, (∑ j ∈ range (i + 1),
            ((j ! : ℚ)⁻¹ * ((i - j) ! : ℚ)⁻¹) • (a ^ j * b ^ (i - j))) := ?_
      _ = ∑ ij ∈ R2N ×ˢ R2N with ij.1 + ij.2 ≤ 2 * N,
            ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := ?_
    · refine sum_congr rfl fun i _ ↦ ?_
      rw [Commute.add_pow h₁ i]
    · simp_rw [smul_sum]
      refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
      simp only [mem_range] at hi hj
      replace hj := Nat.le_of_lt_succ hj
      suffices (i ! : ℚ)⁻¹ * (i.choose j) = ((j ! : ℚ)⁻¹ * ((i - j)! : ℚ)⁻¹) by
        rw [← Nat.cast_commute (i.choose j), ← this, ← mul_smul_comm, ← nsmul_eq_mul,
          mul_smul, ← smul_assoc, smul_comm, smul_assoc]
        norm_cast
      rw [Nat.choose_eq_factorial_div_factorial hj,
        Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hj) (by positivity)]
      simp [field]
    · rw [hR2N, sum_sigma']
      apply sum_bij (fun ⟨i, j⟩ _ ↦ (j, i - j))
      · simp only [mem_sigma, mem_range, mem_filter, mem_product, and_imp]
        cutsat
      · simp only [mem_sigma, mem_range, Prod.mk.injEq, and_imp]
        rintro ⟨x₁, y₁⟩ - h₁ ⟨x₂, y₂⟩ - h₂ h₃ h₄
        simp_all
        cutsat
      · simp only [mem_filter, mem_product, mem_range, mem_sigma, exists_prop, Sigma.exists,
          and_imp, Prod.forall, Prod.mk.injEq]
        exact fun x y _ _ _ ↦ ⟨x + y, x, by cutsat⟩
      · simp only [mem_sigma, mem_range, implies_true]
  have z₁ : ∑ ij ∈ R2N ×ˢ R2N with ¬ ij.1 + ij.2 ≤ 2 * N,
      ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi ↦ by
      rw [mem_filter] at hi
      cases le_or_gt (N + 1) i.1 with
        | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
        | inr _ => rw [pow_eq_zero_of_le (by linarith) h₅, mul_zero, smul_zero]
  have split₁ := sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
    (fun ij ↦ ij.1 + ij.2 ≤ 2 * N)
    (fun ij ↦ ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₁, add_zero] at split₁
  rw [split₁] at s₁
  have z₂ : ∑ ij ∈ R2N ×ˢ R2N with ¬ (ij.1 ≤ N ∧ ij.2 ≤ N),
      ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) = 0 :=
    sum_eq_zero fun i hi ↦ by
    simp only [not_and, not_le, mem_filter] at hi
    cases le_or_gt (N + 1) i.1 with
      | inl h => rw [pow_eq_zero_of_le h h₄, zero_mul, smul_zero]
      | inr h => rw [pow_eq_zero_of_le (hi.2 (Nat.le_of_lt_succ h)) h₅, mul_zero, smul_zero]
  have split₂ := sum_filter_add_sum_filter_not (R2N ×ˢ R2N)
    (fun ij ↦ ij.1 ≤ N ∧ ij.2 ≤ N)
    (fun ij ↦ ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2))
  rw [z₂, add_zero] at split₂
  rw [← split₂] at s₁
  have restrict : ∑ ij ∈ R2N ×ˢ R2N with ij.1 ≤ N ∧ ij.2 ≤ N,
      ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) =
        ∑ ij ∈ RN ×ˢ RN, ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := by
    apply sum_congr
    · ext x
      simp only [mem_filter, mem_product, mem_range, hR2N, hRN]
      cutsat
    · tauto
  rw [restrict] at s₁
  have s₂ := by
    calc (∑ i ∈ RN, (i ! : ℚ)⁻¹ • a ^ i) * ∑ i ∈ RN, (i ! : ℚ)⁻¹ • b ^ i
        = ∑ i ∈ RN, ∑ j ∈ RN, ((i ! : ℚ)⁻¹ * (j ! : ℚ)⁻¹) • (a ^ i * b ^ j) := ?_
      _ = ∑ ij ∈ RN ×ˢ RN, ((ij.1 ! : ℚ)⁻¹ * (ij.2 ! : ℚ)⁻¹) • (a ^ ij.1 * b ^ ij.2) := ?_
    · rw [sum_mul_sum]
      refine sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    · rw [sum_sigma']
      apply sum_bijective (fun ⟨i, j⟩ ↦ (i, j))
      · exact ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h ↦ by cases h; rfl, fun ⟨i, j⟩ ↦ ⟨⟨i, j⟩, rfl⟩⟩
      · simp only [mem_sigma, mem_product, implies_true]
      · simp only [implies_true]
  rwa [s₂.symm] at s₁

@[simp]
theorem exp_zero :
    exp (0 : A) = 1 := by
  simp [exp_eq_sum (pow_one 0)]

theorem exp_mul_exp_neg_self {a : A} (h : IsNilpotent a) :
    exp a * exp (-a) = 1 := by
  simp [← exp_add_of_commute (Commute.neg_right rfl) h h.neg]

theorem exp_neg_mul_exp_self {a : A} (h : IsNilpotent a) :
    exp (-a) * exp a = 1 := by
  simp [← exp_add_of_commute (Commute.neg_left rfl) h.neg h]

theorem isUnit_exp {a : A} (h : IsNilpotent a) : IsUnit (exp a) := by
  apply isUnit_iff_exists.2
  use exp (-a)
  exact ⟨exp_mul_exp_neg_self h, exp_neg_mul_exp_self h⟩

theorem map_exp {B F : Type*} [Ring B] [FunLike F A B] [RingHomClass F A B] [Module ℚ B]
    {a : A} (ha : IsNilpotent a) (f : F) :
    f (exp a) = exp (f a) := by
  obtain ⟨k, hk⟩ := ha
  have hk' : (f a) ^ k = 0 := by simp [← map_pow, hk]
  simp [exp_eq_sum hk, exp_eq_sum hk', map_rat_smul]

theorem exp_smul {G : Type*} [Monoid G] [MulSemiringAction G A]
    (g : G) {a : A} (ha : IsNilpotent a) :
    exp (g • a) = g • exp a :=
  (map_exp ha (MulSemiringAction.toRingHom G A g)).symm

end IsNilpotent

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module ℚ M] [Module ℚ N]

open IsNilpotent TensorProduct

theorem commute_exp_left_of_commute
    {fM : Module.End R M} {fN : Module.End R N} {g : M →ₗ[R] N}
    (hfM : IsNilpotent fM)
    (hfN : IsNilpotent fN)
    (h : fN ∘ₗ g = g ∘ₗ fM) :
    exp fN ∘ₗ g = g ∘ₗ exp fM := by
  ext m
  obtain ⟨k, hfM⟩ := hfM
  obtain ⟨l, hfN⟩ := hfN
  let kl := max k l
  replace hfM : fM ^ kl = 0 := pow_eq_zero_of_le (by omega) hfM
  replace hfN : fN ^ kl = 0 := pow_eq_zero_of_le (by omega) hfN
  have (i : ℕ) : (fN ^ i) (g m) = g ((fM ^ i) m) := by
    simpa using LinearMap.congr_fun (Module.End.commute_pow_left_of_commute h i) m
  simp [exp_eq_sum hfM, exp_eq_sum hfN, this, map_rat_smul]

theorem exp_mul_of_derivation (R B : Type*) [CommRing R] [NonUnitalNonAssocRing B]
    [Module R B] [SMulCommClass R B B] [IsScalarTower R B B] [Module ℚ B]
    (D : B →ₗ[R] B) (h_der : ∀ x y, D (x * y) = x * D y + (D x) * y)
    (h_nil : IsNilpotent D) (x y : B) :
    exp D (x * y) = (exp D x) * (exp D y) := by
  let DL : Module.End R (B ⊗[R] B) := D.lTensor B
  let DR : Module.End R (B ⊗[R] B) := D.rTensor B
  have h_nilL : IsNilpotent DL := h_nil.map <| lTensorAlgHom R B B
  have h_nilR : IsNilpotent DR := h_nil.map <| rTensorAlgHom R B B
  have h_comm : Commute DL DR := by ext; simp [DL, DR]
  set m : B ⊗[R] B →ₗ[R] B := LinearMap.mul' R B with hm
  have h₁ : exp D (x * y) = m (exp (DL + DR) (x ⊗ₜ[R] y)) := by
    suffices exp D ∘ₗ m = m ∘ₗ exp (DL + DR) by simpa using LinearMap.congr_fun this (x ⊗ₜ[R] y)
    apply commute_exp_left_of_commute (h_comm.isNilpotent_add h_nilL h_nilR) h_nil
    ext
    simp [DL, DR, hm, h_der]
  have h₂ : exp DL = (exp D).lTensor B := (h_nil.map_exp (lTensorAlgHom R B B)).symm
  have h₃ : exp DR = (exp D).rTensor B := (h_nil.map_exp (rTensorAlgHom R B B)).symm
  simp [h₁, exp_add_of_commute h_comm h_nilL h_nilR, h₂, h₃, hm]

end Module.End
