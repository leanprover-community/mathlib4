/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Unramified.Basic

/-!

# Formal-unramification of finite products of rings

## Main result

- `Algebra.FormallyUnramified.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-smooth
  if and only if each `A i` is `R`-formally-smooth.

-/

namespace Algebra.FormallyUnramified

universe u v

variable {R : Type max u v} {I : Type v} [Finite I] (f : I → Type max u v)
variable [CommRing R] [∀ i, CommRing (f i)] [∀ i, Algebra R (f i)]

theorem pi_iff :
    FormallyUnramified R (∀ i, f i) ↔ ∀ i, FormallyUnramified R (f i) := by
  classical
  cases nonempty_fintype I
  constructor
  · intro _ i
    exact FormallyUnramified.of_surjective (Pi.evalAlgHom R f i) (Function.surjective_eval i)
  · intro H
    rw [iff_comp_injective]
    intros B _ _ J hJ f₁ f₂ e
    ext g
    rw [← Finset.univ_sum_single g, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro x -
    have hf : ∀ x, f₁ x - f₂ x ∈ J := by
      intro g
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact AlgHom.congr_fun e g
    let e : ∀ i, f i := Pi.single x 1
    have he : IsIdempotentElem e := by simp [IsIdempotentElem, e, ← Pi.single_mul]
    have h₁ : (f₁ e) * (1 - f₂ e) = 0 := by
      rw [← Ideal.mem_bot, ← hJ, ← ((he.map f₁).mul (he.map f₂).one_sub).eq, ← pow_two]
      apply Ideal.pow_mem_pow
      convert Ideal.mul_mem_left _ (f₁ e) (hf e) using 1
      rw [mul_sub, mul_sub, mul_one, (he.map f₁).eq]
    have h₂ : (f₂ e) * (1 - f₁ e) = 0 := by
      rw [← Ideal.mem_bot, ← hJ, ← ((he.map f₂).mul (he.map f₁).one_sub).eq, ← pow_two]
      apply Ideal.pow_mem_pow
      convert Ideal.mul_mem_left _ (-f₂ e) (hf e) using 1
      rw [neg_mul, mul_sub, mul_sub, mul_one, neg_sub, (he.map f₂).eq]
    have H : f₁ e = f₂ e := by
      trans f₁ e * f₂ e
      · rw [← sub_eq_zero, ← h₁, mul_sub, mul_one]
      · rw [eq_comm, ← sub_eq_zero, ← h₂, mul_sub, mul_one, mul_comm]
    let J' := Ideal.span {1 - f₁ e}
    let f₁' : f x →ₐ[R] B ⧸ J' := by
      apply AlgHom.ofLinearMap
        (((Ideal.Quotient.mkₐ R J').comp f₁).toLinearMap.comp (LinearMap.single _ _ x))
      · simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, LinearMap.coe_single,
          Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [eq_comm, ← sub_eq_zero, ← (Ideal.Quotient.mk J').map_one, ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      · intros r s; simp [Pi.single_mul]
    let f₂' : f x →ₐ[R] B ⧸ J' := by
      apply AlgHom.ofLinearMap
        (((Ideal.Quotient.mkₐ R J').comp f₂).toLinearMap.comp (LinearMap.single _ _ x))
      · simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, LinearMap.coe_single,
          Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [eq_comm, ← sub_eq_zero, ← (Ideal.Quotient.mk J').map_one, ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, H]
      · intros r s; simp [Pi.single_mul]
    suffices f₁' = f₂' by
      have := AlgHom.congr_fun this (g x)
      simp only [AlgHom.comp_toLinearMap, AlgHom.ofLinearMap_apply, LinearMap.coe_comp,
        LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply, ← map_sub,
        Ideal.Quotient.mkₐ_eq_mk, ← sub_eq_zero (b := Ideal.Quotient.mk J' _), sub_zero, f₁', f₂',
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, J'] at this
      obtain ⟨c, hc⟩ := this
      apply_fun (f₁ e * ·) at hc
      rwa [← mul_assoc, mul_sub, mul_sub, mul_one, (he.map f₁).eq, sub_self, zero_mul,
        ← map_mul, H, ← map_mul, ← Pi.single_mul, one_mul, sub_eq_zero] at hc
    apply FormallyUnramified.comp_injective (I := J.map (algebraMap _ _))
    · rw [← Ideal.map_pow, hJ, Ideal.map_bot]
    · ext r
      rw [← sub_eq_zero]
      simp only [Ideal.Quotient.algebraMap_eq, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        Function.comp_apply, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, f₁', f₂',
        AlgHom.comp_toLinearMap, AlgHom.ofLinearMap_apply, LinearMap.coe_comp,
        LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk J') (hf (Pi.single x r))

instance [∀ i, FormallyUnramified R (f i)] : FormallyUnramified R (Π i, f i) :=
  (pi_iff _).mpr ‹_›

end Algebra.FormallyUnramified
