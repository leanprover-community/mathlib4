/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
import Mathlib.Analysis.Fourier.Char
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

/-!
# Characteristic Function of a Finite Measure

This file defines the characteristic function of a finite measure on a topological vector space
`V`.

The characteristic function of a finite measure `P` on `V` is the mapping
`W → ℂ, w => ∫ v, e (-L v w) ∂P`,
where `e` is a continuous additive character and `L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ` is a bilinear map.

A typical example is `V = W = ℝ` and `L v w = v * w`.

## Main definition

`charFun P hL : W → ℂ`: The characteristic function of a Measure `P`, evaluated at `w`, is the
integral of `char he hL w` with respect to `P`, for the standard choice of `e = Circle.expAddChar`.

## Main statements

- `ext_of_integral_char_eq`: Assume `e` and `L` are non-trivial. If the integrals of `char`
  with respect to two finite measures `P` and `P'` coincide, then `P = P'`.
- `ext_of_charFun_eq`: If the characteristic functions of two finite measures `P` and `P'` are
  equal, then `P = P'`. In other words, characteristic functions separate finite measures.

-/

open Filter BoundedContinuousFunction Complex

namespace MeasureTheory

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    {e : AddChar ℝ Circle} {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {he : Continuous e} {hL : Continuous fun p : V × W ↦ L p.1 p.2}

/--
The characteristic function of a Measure `P`, evaluated at `w` is the integral of
`fun v ↦ e (L v w)` with respect to `P` for the standard choice of `e = Circle.exp`.
-/
noncomputable
def charFun [MeasurableSpace V] (P : Measure V) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (w : W) : ℂ :=
  ∫ v, char Circle.continuous_expAddChar hL w v ∂P

section ext

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [PseudoEMetricSpace V] [MeasurableSpace V]
    [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V] {L : V →ₗ[ℝ] W →ₗ[ℝ] ℝ}
    {𝕜 : Type*} [RCLike 𝕜]

/--
If the integrals of `char` with respect to two finite measures `P` and `P'` coincide, then
`P = P'`.
-/
theorem ext_of_integral_char_eq (he : Continuous e) (he' : e ≠ 1)
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (P P' : Measure V) [IsFiniteMeasure P] [IsFiniteMeasure P']
    (h : ∀ w, ∫ v, char he hL w v ∂P = ∫ v, char he hL w v ∂P') :
    P = P' := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
      (separatesPoints_charPoly he he' hL hL')
  intro _ hg
  simp only [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  rw [hw]
  have hsum (P : Measure V) [IsFiniteMeasure P] :
      ∫ v, ∑ a ∈ w.support, w a * e (L v a) ∂P = ∑ a ∈ w.support, ∫ v, w a * e (L v a) ∂P :=
    integral_finset_sum w.support
      fun a ha => Integrable.const_mul (integrable P (char he hL a)) _
  rw [hsum P, hsum P']
  apply Finset.sum_congr rfl fun i _ => ?_
  simp only [smul_eq_mul, MeasureTheory.integral_mul_left, mul_eq_mul_left_iff]
  exact Or.inl (h i)

lemma expAddChar_ne_one : Circle.expAddChar ≠ 1 := by
  rw [DFunLike.ne_iff]
  use Real.pi
  simp only [Circle.expAddChar, AddChar.coe_mk, AddChar.one_apply]
  intro h
  have heq := congrArg Subtype.val h
  rw [Circle.coe_exp Real.pi, Complex.exp_pi_mul_I] at heq
  norm_num at heq

/--
If the characteristic functions of two finite measures `P` and `P'` are equal, then `P = P'`. In
other words, characteristic functions separate finite measures.
-/
theorem ext_of_charFun_eq
    (hL' : ∀ v ≠ 0, L v ≠ 0) (hL : Continuous fun p : V × W ↦ L p.1 p.2)
    (P P' : Measure V) [IsFiniteMeasure P] [IsFiniteMeasure P'] (h : charFun P hL = charFun P' hL) :
    P = P' :=
  ext_of_integral_char_eq Circle.continuous_expAddChar expAddChar_ne_one hL' hL P P'
    (fun w => congrFun h w)

end ext

end MeasureTheory
