module
/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Sébastien Gouëzel, Patrick Massot, Ruben Van de Velde, Floris van Doorn,
Junyan Xu
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Smooth functions whose integral calculates the values of polynomials

In any space `ℝᵈ` and given any `N`, we construct a smooth function supported in the unit ball
whose integral against a multivariate polynomial `P` of total degree at most `N` is `P 0`.

This is a test of the state of the library suggested by Martin Hairer.
-/

noncomputable section

open Metric Set MeasureTheory PiLp
open MvPolynomial hiding support
open Function hiding eval
open scoped ContDiff

variable {ι : Type*} [Fintype ι]

section normed
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The set of `C^n` functions supported in a set `s`, as a submodule of the space of functions. -/
def ContDiffSupportedOn (n : ℕ∞) (s : Set E) : Submodule 𝕜 (E → F) where
  carrier := { f : E → F | tsupport f ⊆ s ∧ ContDiff 𝕜 n f }
  add_mem' hf hg := ⟨(tsupport_add _ _).trans <| union_subset hf.1 hg.1, hf.2.add hg.2⟩
  zero_mem' :=
    ⟨(tsupport_eq_empty_iff.mpr rfl).subset.trans (empty_subset _), contDiff_const (c := 0)⟩
  smul_mem' r f hf :=
    ⟨(closure_mono <| support_const_smul_subset r f).trans hf.1, contDiff_const.smul hf.2⟩

namespace ContDiffSupportedOn

variable {n : ℕ∞} {s : Set E}

instance : FunLike (ContDiffSupportedOn 𝕜 E F n s) E F where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

@[simp]
lemma coe_mk (f : E → F) (h) : (⟨f, h⟩ : ContDiffSupportedOn 𝕜 E F n s) = f := rfl

lemma tsupport_subset (f : ContDiffSupportedOn 𝕜 E F n s) : tsupport f ⊆ s := f.2.1

lemma support_subset (f : ContDiffSupportedOn 𝕜 E F n s) :
    support f ⊆ s := subset_tsupport _ |>.trans (tsupport_subset f)

lemma contDiff (f : ContDiffSupportedOn 𝕜 E F n s) :
    ContDiff 𝕜 n f := f.2.2

theorem continuous (f : ContDiffSupportedOn 𝕜 E F n s) : Continuous f :=
  (ContDiffSupportedOn.contDiff _).continuous

lemma hasCompactSupport [ProperSpace E] (f : ContDiffSupportedOn 𝕜 E F n (closedBall 0 1)) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1) (support_subset f)

theorem integrable_eval_mul (p : MvPolynomial ι ℝ)
    (f : ContDiffSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :
    Integrable fun (x : EuclideanSpace ℝ ι) ↦ eval x p * f x :=
  (p.continuous_eval.comp (continuous_ofLp 2 _)).mul
    (ContDiffSupportedOn.contDiff f).continuous
    |>.integrable_of_hasCompactSupport (hasCompactSupport f).mul_left

end ContDiffSupportedOn

end normed
open ContDiffSupportedOn

variable (ι)
/-- Interpreting a multivariate polynomial as an element of the dual of smooth functions supported
in the unit ball, via integration against Lebesgue measure. -/
def L : MvPolynomial ι ℝ →ₗ[ℝ]
    Module.Dual ℝ (ContDiffSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :=
  have int := ContDiffSupportedOn.integrable_eval_mul (ι := ι)
  .mk₂ ℝ (fun p f ↦ ∫ x : EuclideanSpace ℝ ι, eval x p • f x)
    (fun p₁ p₂ f ↦ by simp [add_mul, integral_add (int p₁ f) (int p₂ f)])
    (fun r p f ↦ by simp [mul_assoc, integral_const_mul])
    (fun p f₁ f₂ ↦ by simp_rw [smul_eq_mul, ← integral_add (int p _) (int p _), ← mul_add]; rfl)
    fun r p f ↦ by simp_rw [← integral_smul, smul_comm r]; rfl

lemma inj_L : Injective (L ι) :=
  (injective_iff_map_eq_zero _).mpr fun p hp ↦ by
    have H : ∀ᵐ x : EuclideanSpace ℝ ι, x ∈ ball 0 1 → eval x p = 0 :=
      isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (p.continuous_eval.comp (continuous_ofLp 2 _)
          |>.locallyIntegrable.locallyIntegrableOn _)
        fun g hg _h2g g_supp ↦ by
          simpa [mul_comm (g _), L] using congr($hp ⟨g, g_supp.trans ball_subset_closedBall, hg⟩)
    simp_rw [MvPolynomial.funext_iff, map_zero]
    refine fun x ↦ AnalyticOnNhd.eval_linearMap (EuclideanSpace.equiv ι ℝ).toLinearMap p
      |>.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (preconnectedSpace_iff_univ.mp inferInstance) (z₀ := 0) trivial
      (Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one) ?_) trivial
    rw [← ae_restrict_iff'₀ measurableSet_ball.nullMeasurableSet] at H
    apply Measure.eqOn_of_ae_eq H
      (p.continuous_eval.comp (continuous_ofLp 2 _)).continuousOn continuousOn_const
    rw [isOpen_ball.interior_eq]
    apply subset_closure

set_option backward.isDefEq.respectTransparency false in
lemma hairer (N : ℕ) (ι : Type*) [Fintype ι] :
    ∃ (ρ : EuclideanSpace ℝ ι → ℝ), tsupport ρ ⊆ closedBall 0 1 ∧ ContDiff ℝ ∞ ρ ∧
    ∀ (p : MvPolynomial ι ℝ), p.totalDegree ≤ N →
    ∫ x : EuclideanSpace ℝ ι, eval x p • ρ x = eval 0 p := by
  have := (inj_L ι).comp (restrictTotalDegree ι ℝ N).injective_subtype
  rw [← LinearMap.coe_comp] at this
  obtain ⟨⟨φ, supφ, difφ⟩, hφ⟩ :=
    LinearMap.flip_surjective_iff₁.2 this ((aeval 0).toLinearMap.comp <| Submodule.subtype _)
  exact ⟨φ, supφ, difφ, fun P hP ↦ congr($hφ ⟨P, (mem_restrictTotalDegree ι N P).mpr hP⟩)⟩
