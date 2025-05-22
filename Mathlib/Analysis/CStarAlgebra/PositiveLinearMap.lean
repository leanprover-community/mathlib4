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
  [StarOrderedRing B₁]

lemma apply_le_of_isSelfAdjoint (f : B₁ →ₚ[ℂ] B₂) (x : B₁) (hx : IsSelfAdjoint x) :
    f x ≤ f (algebraMap ℝ B₁ ‖x‖) := by
  gcongr
  exact IsSelfAdjoint.le_algebraMap_norm_self hx

lemma norm_apply_le_of_nonneg [StarOrderedRing B₂] (f : B₁ →ₚ[ℂ] B₂) (x : B₁) (hx : 0 ≤ x) :
    ‖f x‖ ≤ ‖f 1‖ * ‖x‖ := by
  have h : ‖‖x‖‖ = ‖x‖ := by simp
  rw [mul_comm, ← h, ← norm_smul ‖x‖ (f 1)]
  clear h
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg hx) ?_
  rw [← Complex.coe_smul, ← LinearMapClass.map_smul f]
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
  by_contra! hcontra
  -- Given `n : ℕ`, we can always choose a positive element of norm one with `2 ^ (2 * n) < ‖f x‖`
  have (n : ℕ) : ∃ x, 0 ≤ x ∧ ‖x‖ = 1 ∧ 2 ^ (2 * n) < ‖f x‖ := by
    obtain ⟨hx₁, hx₂⟩ := Classical.choose_spec (hcontra (2 ^ (2 * n)))
    set x := Classical.choose (hcontra (2 ^ (2 * n)))
    have hx := (eq_zero_or_norm_pos x).resolve_left (fun hx ↦ by simp_all)
    refine ⟨‖x‖⁻¹ • x, smul_nonneg (by positivity) hx₁, ?_, ?_⟩
    · simp [norm_smul, inv_mul_cancel₀ hx.ne']
    · simpa [norm_smul] using (lt_inv_mul_iff₀' hx).mpr hx₂
  -- Let `x n` be a sequence of nonnegative elements such that `‖x n‖ = 1` and `‖f (x n)‖ ≥ 4 ^ n`.
  choose x hx using this
  simp only [forall_and] at hx
  obtain ⟨hx_nonneg, hx_norm, hx⟩ := hx
  -- `∑ n, 2 ^ (-n) • x n` converges
  have x_summable : Summable fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ)) • x n := by
    refine Summable.of_norm ?_
    have : (2 : ℝ)⁻¹ < 1 := by norm_num
    simp [norm_smul, hx_norm, ← inv_pow, this]
  -- There is some `n` such that `‖f (∑' m, 2 ^ (-m) • x m)‖ < 2 ^ n`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖f (∑' (n : ℕ), (2 : ℝ) ^ (-(n : ℤ)) • x n)‖ < (2 : ℝ) ^ n :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two |>.eventually_gt_atTop _
      |>.exists
  -- But `2 ^ n ≤ ‖f (2 ^ (-n) • x n)‖ ≤ ‖f (∑' m, 2 ^ (-m) • x m)‖`, which is a contradiction.
  apply hn.not_ge
  trans ‖f ((2 : ℝ) ^ (-n : ℤ) • x n)‖
  · have := hx n |>.le
    rw [pow_mul', sq] at this
    simpa [norm_smul] using (le_inv_mul_iff₀' (show 0 < (2 : ℝ) ^ n by positivity)).mpr this
  · have (m : ℕ) : 0 ≤ ((2 : ℝ) ^ (-(m : ℤ)) • x m) := smul_nonneg (by positivity) (hx_nonneg m)
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (f.map_nonneg (this n)) ?_
    gcongr
    exact x_summable.le_tsum n fun m _ ↦ this m

instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
    ContinuousLinearMapClass F ℂ A₁ A₂ where
  map_continuous f := by
    have hbound : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C * ‖a‖ := by
      obtain ⟨C, h⟩ := exists_norm_apply_le (f : A₁ →ₚ[ℂ] A₂)
      exact ⟨C, h⟩
    exact (LinearMap.mkContinuousOfExistsBound (f : A₁ →ₗ[ℂ] A₂) hbound).continuous

instance {F : Type*} [FunLike F A₁ A₂] [LinearMapClass F ℂ A₁ A₂] [OrderHomClass F A₁ A₂] :
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
