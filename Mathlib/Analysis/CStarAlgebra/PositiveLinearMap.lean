/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-! # Positive linear maps in C⋆-algebras

This file develops the API for positive linear maps over C⋆-algebras.

## Main results

* `PositiveLinearMap.exists_norm_apply_le`: positive maps are bounded (and therefore continuous)
  on non-unital C⋆-algebras.

## References

* The proof that positive maps are bounded was taken from
https://math.stackexchange.com/questions/426487/why-is-every-positive-linear-map-between-c-algebras-bounded
-/

open scoped NNReal

variable {A₁ A₂ B₁ B₂ : Type*}

section CFC

variable [NonUnitalRing A₁] [Module ℂ A₁] [SMulCommClass ℝ A₁ A₁] [IsScalarTower ℝ A₁ A₁]
  [StarRing A₁] [TopologicalSpace A₁] [NonUnitalContinuousFunctionalCalculus ℝ A₁ IsSelfAdjoint]
  [PartialOrder A₁] [StarOrderedRing A₁]

variable [NonUnitalRing A₂] [Module ℂ A₂] [StarRing A₂] [PartialOrder A₂] [StarOrderedRing A₂]

@[aesop safe apply (rule_sets := [CStarAlgebra])]
lemma map_isSelfAdjoint (f : A₁ →ₚ[ℂ] A₂) (a : A₁) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (f a) := by
  rw [← CFC.posPart_sub_negPart a ha]
  cfc_tac

end CFC


section CStarAlgebra

namespace PositiveLinearMap

variable [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂] [PartialOrder A₁]
  [StarOrderedRing A₁] [PartialOrder A₂] [StarOrderedRing A₂]
  [CStarAlgebra B₁] [CStarAlgebra B₂] [PartialOrder B₁] [PartialOrder B₂]
  [StarOrderedRing B₁] [StarOrderedRing B₂]

lemma apply_le_of_isSelfAdjoint (f : B₁ →ₚ[ℂ] B₂) (x : B₁) (hx : IsSelfAdjoint x) :
    f x ≤ f (algebraMap ℝ B₁ ‖x‖) := by
  gcongr
  exact IsSelfAdjoint.le_algebraMap_norm_self hx

lemma norm_apply_le_of_nonneg (f : B₁ →ₚ[ℂ] B₂) (x : B₁) (hx : 0 ≤ x) :
    ‖f x‖ ≤ ‖f 1‖ * ‖x‖ := by
  have h : ‖‖x‖‖ = ‖x‖ := by simp
  rw [mul_comm, ← h, ← norm_smul ‖x‖ (f 1)]
  clear h
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg hx) ?_
  change f x ≤ (‖x‖ : ℂ) • f 1
  rw [← LinearMapClass.map_smul f]
  gcongr
  rw [← Algebra.algebraMap_eq_smul_one]
  exact IsSelfAdjoint.le_algebraMap_norm_self <| .of_nonneg hx

open Complex Filter in
/--
If `f` is a positive map, then it is bounded (and therefore continuous).
-/
lemma exists_norm_apply_le (f : A₁ →ₚ[ℂ] A₂) : ∃ C : ℝ≥0, ∀ a, ‖f a‖ ≤ C * ‖a‖ := by
  /- It suffices to only consider for positive `a`, by decomposing `a` into positive and negative
     parts of the real and imaginary parts. -/
  suffices h_nonneg : ∃ C : ℝ≥0, ∀ a, 0 ≤ a → ‖f a‖ ≤ C * ‖a‖ by
    obtain ⟨C, hmain⟩ := h_nonneg
    refine ⟨4 * C, fun x ↦ ?_⟩
    obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg x
    conv_lhs => rw [hy]
    simp only [map_sum, map_smul, NNReal.coe_add]
    apply norm_sum_le _ _ |>.trans
    simp only [norm_smul, norm_pow, norm_I, one_pow, one_mul]
    apply Finset.sum_le_sum (g := fun _ ↦ C * ‖x‖) (fun i _ ↦ ?_) |>.trans <| by simp [mul_assoc]
    apply hmain _ (hy_nonneg i) |>.trans
    simp only
    gcongr
    exact hy_norm i
  -- Let's proceed by contradiction
  by_contra hcontra
  push_neg at hcontra
  let x' n := Classical.choose (hcontra (2 ^ (2 * n)))
  have hx' n := Classical.choose_spec (hcontra ((2 : ℝ≥0) ^ (2 * n)))
  -- Let `x n` be a sequence such that `‖x n‖ = 1` and `‖f (x n)‖ ≥ 4^n`.
  let x n := ‖x' n‖⁻¹ • x' n
  have hnz : ∀ n, x' n ≠ 0 := by
    by_contra H
    push_neg at H
    obtain ⟨m, hm⟩ := H
    unfold x' at hm
    specialize hx' m
    simp [hm] at hx'
  have hx : ∀ n, 0 ≤ x n ∧ 2 ^ (2 * n) < ‖f (x n)‖ := fun n => by
    refine ⟨smul_nonneg (by positivity) (hx' n).1, ?_⟩
    unfold x
    simp only [f.map_smul_of_tower, norm_smul, norm_inv, Complex.norm_real,
      norm_norm, gt_iff_lt]
    rw [lt_inv_mul_iff₀ (norm_pos_iff.mpr (hnz n)), mul_comm]
    exact (hx' n).2
  have hx_norm : ∀ n, ‖x n‖ = 1 := by
    intro n
    unfold x
    have : ‖x' n‖ ≠ 0 := by aesop
    simp [norm_smul, inv_mul_cancel₀ this]
  -- Consider the sum `∑ n, 2^{-n} • x n`.
  let xsum := ∑' (n : ℕ), (2 : ℝ) ^ (-(n : ℤ)) • x n
  -- This sum converges to some element
  have x_summable : Summable fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ)) • x n := by
    refine Summable.of_norm ?_
    have : (2 : ℝ)⁻¹ < 1 := by norm_num
    simp [norm_smul, hx_norm, ← inv_pow, this]
  -- Then `f` applied to a single term of the sum is upper-bounded by `f xsum`,
  -- and, taking norms, `‖f xsum‖ ≥ 2 ^ n` for any `n`, which is a contradiction.
  have h₁ : ∀ n : ℕ, f ((2 : ℝ) ^ (-(n : ℤ)) • x n) ≤ f xsum := by
    intro n
    gcongr
    exact le_tsum x_summable _ fun j hj => smul_nonneg (by positivity) (hx j).1
  have h₂ : ∀ n : ℕ, 2 ^ n ≤ ‖f xsum‖ := fun n => by
    calc _ = (2 : ℝ) ^ (n : ℤ) := rfl
      _ = (2 : ℝ) ^ (-(n : ℤ)) * 2 ^ (2 * (n : ℤ)) := by
          rw [← zpow_add₀ (a := 2) (by norm_num) (-n) (2 * n)]
          congr
          ring
      _ ≤ ‖f ((2 : ℝ) ^ (-(n : ℤ)) • x n)‖ := by
          simp only [f.map_smul_of_tower, zpow_neg, zpow_natCast, norm_smul,
            norm_inv, norm_pow, Real.norm_ofNat, inv_pos, Nat.ofNat_pos, pow_pos, mul_le_mul_left]
          exact le_of_lt (hx n).2
      _ ≤ ‖f xsum‖ := by
          refine CStarAlgebra.norm_le_norm_of_nonneg_of_le ?_ (h₁ n)
          exact f.map_nonneg <| smul_nonneg (by positivity) (hx n).1
  have h₃ : ∃ n : ℕ, ⌈‖f xsum‖⌉₊ < (2 : ℝ) ^ n := by
    refine Eventually.exists (f := atTop) ?_
    refine Tendsto.eventually_gt_atTop ?_ _
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨n, hn⟩ := h₃
  have hfinal : (2 : ℝ) ^ n < 2 ^ n := calc
    _ ≤ ‖f xsum‖ := h₂ n
    _ ≤ ⌈‖f xsum‖⌉₊ := Nat.le_ceil ‖f xsum‖
    _ < 2 ^ n := hn
  linarith

instance {F : Type*} [FunLike F A₁ A₂] [PositiveLinearMapClass F ℂ A₁ A₂] :
    ContinuousLinearMapClass F ℂ A₁ A₂ where
  map_continuous f := by
    have hbound : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C * ‖a‖ := by
      obtain ⟨C, h⟩ := exists_norm_apply_le (f : A₁ →ₚ[ℂ] A₂)
      exact ⟨C, h⟩
    exact (LinearMap.mkContinuousOfExistsBound (f : A₁ →ₗ[ℂ] A₂) hbound).continuous

instance {F : Type*} [FunLike F A₁ A₂] [PositiveLinearMapClass F ℂ A₁ A₂] :
    StarHomClass F A₁ A₂ where
  map_star f a := by
    obtain ⟨y, hy_nonneg, hy_norm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg a
    have hy' : ∀ x : Fin 4, star (y x) = y x := fun x => by
      rw [IsSelfAdjoint.star_eq (hy_nonneg x).isSelfAdjoint]
    have hy'' : ∀ x : Fin 4, star (f (y x)) = f (y x) := fun x => by
      rw [IsSelfAdjoint.star_eq (map_nonneg f (hy_nonneg x)).isSelfAdjoint]
    simp [hy, hy', hy'']

end PositiveLinearMap

end CStarAlgebra
