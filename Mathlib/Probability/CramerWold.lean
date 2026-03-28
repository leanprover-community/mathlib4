/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section

open Mathlib MeasureTheory ProbabilityTheory Topology Filter Vector Complex Isometry BoundedContinuousFunction Finset RealInnerProductSpace ProbabilityMeasure Measurable

open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω} {Ω' : Type*}
[MeasurableSpace Ω'] {Q : ProbabilityMeasure Ω'} {d : ℕ+} {X : Ω' → EuclideanSpace ℝ (Fin d)}
{Xn : ℕ → Ω → EuclideanSpace ℝ (Fin d)}

lemma measurable_dotProduct_shorter {n : ℕ} (hX : Measurable (Xn n)) (t : EuclideanSpace ℝ (Fin d)):
  Measurable (fun ω : Ω => ⟪((Xn n) ω), t⟫) :=
  Measurable.inner_const hX

lemma aemeasurable_dotProduct {n : ℕ} {μ : Measure Ω} (hX : Measurable (Xn n))
(t : EuclideanSpace ℝ (Fin d)):
  AEMeasurable (fun ω : Ω => ⟪((Xn n) ω), t⟫) μ :=
  (measurable_dotProduct_shorter hX t).aemeasurable

lemma measurable_dotProduct' (hX : Measurable X) (t : EuclideanSpace ℝ (Fin d)):
  Measurable (fun ω : Ω' => ⟪(X ω), t⟫) :=
  Measurable.inner_const hX

lemma aemeasurable_dotProduct' {μ : Measure Ω'} (hX : Measurable X) (t : EuclideanSpace ℝ (Fin d)):
  AEMeasurable (fun ω : Ω' => ⟪(X ω), t⟫) μ :=
  (measurable_dotProduct' hX t).aemeasurable

lemma continuous_exp_ofReal_mul_I : Continuous (fun u : ℝ => Complex.exp (u * Complex.I))
  := continuous_exp.comp (Continuous.mul continuous_ofReal continuous_const)

lemma complex_dist_zero_eq_abs (z : ℂ) : dist z 0 = ‖z‖ :=
calc
  dist z 0 = ‖z - 0‖ := by simp
  _ = ‖z‖ := by rw [sub_zero]

lemma complex_dist_zero_eq_abs' (z : ℂ) : dist 0 z = ‖z‖ :=
by rw [dist_comm, complex_dist_zero_eq_abs z]

lemma cexp_bound_exact : ∀ (u v : ℝ), dist (Complex.exp (↑u * I)) (Complex.exp (↑v * I)) ≤ 2 :=
  fun u v =>
    calc
      dist (Complex.exp (↑u * I)) (Complex.exp (↑v * I))
        ≤ dist (Complex.exp (↑u * I)) 0 + dist 0 (Complex.exp (↑v * I)) := dist_triangle _ _ _
      _ = ‖Complex.exp (↑u * I)‖ + ‖Complex.exp (↑v * I)‖ := by rw [complex_dist_zero_eq_abs, complex_dist_zero_eq_abs']
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

def bounded_continuous_exp_ofReal_mul_I : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound ⟨fun u => Complex.exp (u * Complex.I), continuous_exp_ofReal_mul_I⟩ 2 cexp_bound_exact

def bounded_continuous_exp_inner_mul_I (t : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) →ᵇ ℂ :=
  BoundedContinuousFunction.compContinuous bounded_continuous_exp_ofReal_mul_I ⟨fun x => ⟪x, t⟫,
    continuous_id.inner continuous_const⟩

@[simp] lemma bounded_continuous_exp_ofReal_mul_I_eq_cexp (u : ℝ) :
  bounded_continuous_exp_ofReal_mul_I u = Complex.exp (u * Complex.I) :=
rfl

lemma charFun_tendsto_if_inner_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)):
  (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct (hXn n) t)) atTop (𝓝 (Q.map (aemeasurable_dotProduct' hX t)))) → (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t) atTop (𝓝 (charFun (Q.map hX.aemeasurable) t))) :=
  by
    intros hconv t
    let φ := bounded_continuous_exp_inner_mul_I t

    let ψ := bounded_continuous_exp_ofReal_mul_I
    let ψ_re := (fun u => (ψ u).re)
    let ψ_im := (fun u => (ψ u).im)

    have ψ_re_bcf_bound_exact : ∀ (u v : ℝ), dist (ψ_re u) (ψ_re v) ≤ 2 := fun u v =>
    calc
      dist (ψ_re u) (ψ_re v)
        ≤ dist (ψ_re u) 0 + dist 0 (ψ_re v) := dist_triangle _ _ _
      _ = |ψ_re u| + |ψ_re v| := by rw [Real.dist_0_eq_abs, dist_comm, Real.dist_0_eq_abs]
      _ = ‖ψ_re u‖ + ‖ψ_re v‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ψ u‖ + ‖ψ v‖ :=
      by
        simp [ψ_im]
        exact add_le_add (RCLike.norm_re_le_norm (ψ u)) (RCLike.norm_re_le_norm (ψ v))
      _ = ‖Complex.exp (u * Complex.I)‖ + ‖Complex.exp (v * Complex.I)‖ := by simp [ψ, ψ]
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

    have ψ_im_bcf_bound_exact : ∀ (u v : ℝ), dist (ψ_im u) (ψ_im v) ≤ 2 := fun u v =>
    calc
      dist (ψ_im u) (ψ_im v)
        ≤ dist (ψ_im u) 0 + dist 0 (ψ_im v) := dist_triangle _ _ _
      _ = |ψ_im u| + |ψ_im v| := by rw [Real.dist_0_eq_abs, dist_comm, Real.dist_0_eq_abs]
      _ = ‖ψ_im u‖ + ‖ψ_im v‖ := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ‖ψ u‖ + ‖ψ v‖ :=
      by
        simp [ψ_im]
        exact add_le_add (RCLike.norm_im_le_norm (ψ u)) (RCLike.norm_im_le_norm (ψ v))
      _ = ‖Complex.exp (u * Complex.I)‖ + ‖Complex.exp (v * Complex.I)‖ := by simp [ψ, ψ]
      _ = 1 + 1 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]
      _ = 2 := by norm_num

    let ψ_re_bcf : ℝ →ᵇ ℝ :=
      .mkOfBound ⟨ψ_re, continuous_re.comp ψ.continuous⟩ 2 ψ_re_bcf_bound_exact
    let ψ_im_bcf : ℝ →ᵇ ℝ :=
      .mkOfBound ⟨ψ_im, continuous_im.comp ψ.continuous⟩ 2 ψ_im_bcf_bound_exact

    let ψ_decomp (x : ℝ) : ψ x = ψ_re_bcf x + (ψ_im_bcf x) * Complex.I :=
      by
        simp [ψ_re_bcf, ψ_im_bcf]
        rw [Complex.re_add_im]

    let h_lim (f : ℝ →ᵇ ℝ) : 0 ≤ f → atTop.limsup (fun n => ∫ x, f x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) ≤ ∫ x, f x ∂ (↑(Q.map (aemeasurable_dotProduct' hX t))) :=
      by
        intro _
        rw [Tendsto.limsup_eq]
        haveI := @tendsto_iff_forall_integral_tendsto ℝ _ _ _ ℕ atTop (fun n => P.map (aemeasurable_dotProduct (hXn n) t)) (Q.map (aemeasurable_dotProduct' hX t) : ProbabilityMeasure ℝ)
        haveI := Iff.mp this (hconv t)
        apply this f

    have integralConv_re2 :
      Tendsto (fun n => ∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ_re_bcf x ∂ (↑(Q.map (aemeasurable_dotProduct' hX t))))) := by

        haveI := @tendsto_iff_forall_integral_tendsto ℝ _ _ _ ℕ atTop (fun n => P.map (aemeasurable_dotProduct (hXn n) t)) (Q.map (aemeasurable_dotProduct' hX t) : ProbabilityMeasure ℝ)
        haveI := Iff.mp this (hconv t)
        apply this ψ_re_bcf


    have integralConv_re :
      Tendsto (fun n => ∫ (x : ℝ), ψ_re_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ_re_bcf x ∂ (↑(Q.map (aemeasurable_dotProduct' hX t))))) := BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integral h_lim ψ_re_bcf

    have integralConv_im :
      Tendsto (fun n => ∫ (x : ℝ), ψ_im_bcf x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ_im_bcf x ∂ (↑(Q.map (aemeasurable_dotProduct' hX t)))) ) :=
      BoundedContinuousFunction.tendsto_integral_of_forall_limsup_integral_le_integral h_lim ψ_im_bcf

    have h_ψ : ∀ (ν : ProbabilityMeasure ℝ), ∫ x, ψ x ∂ ν = ∫ x, ψ_re_bcf x ∂ ν + (∫ x, ψ_im_bcf x ∂ ν) * Complex.I :=
      by
        intro ν
        simp_rw [ψ_decomp]
        have h_re : ∫ x, ((ψ_re_bcf x : ℂ)) ∂ ν = (∫ x, ψ_re_bcf x ∂ ν : ℂ) :=
          by simp [integral_complex_ofReal]

        have h_im_mul : ∫ x, ((ψ_im_bcf x : ℂ) * Complex.I) ∂ ν
            = (∫ x, (ψ_im_bcf x : ℂ) ∂ ν) * Complex.I :=
          by
            simpa using (integral_mul_const (Complex.I) (fun x : ℝ => (ψ_im_bcf x : ℂ)))

        have h_im : (∫ x, (ψ_im_bcf x : ℂ) ∂ ν) = (∫ x, ψ_im_bcf x ∂ ν : ℂ) :=
          by simp [integral_complex_ofReal]

        rw [integral_add, h_re, h_im_mul, h_im]
        rw [←integral_complex_ofReal, ←integral_complex_ofReal]

        apply (ψ_re_bcf.integrable ν).ofReal
        apply (ψ_im_bcf.integrable ν).ofReal.mul_const Complex.I

    have integralConv :
      Tendsto (fun n => ∫ (x : ℝ), ψ x ∂ (↑(P.map (aemeasurable_dotProduct (hXn n) t)))) atTop (𝓝 (∫ (x : ℝ), ψ x ∂ (↑(Q.map (aemeasurable_dotProduct' hX t))))) :=
        by
          rw [h_ψ]
          apply Tendsto.congr (fun _ => (h_ψ _).symm)
          apply Tendsto.add (Tendsto.ofReal integralConv_re)
          apply Tendsto.mul
          exact Tendsto.ofReal integralConv_im
          simp

    simp only [charFun, toMeasure_map]
    rw [MeasureTheory.integral_map hX.aemeasurable ?_]
    · rw [←MeasureTheory.integral_map (aemeasurable_dotProduct' hX t) (continuous_exp_ofReal_mul_I.stronglyMeasurable.aestronglyMeasurable)]
      apply Tendsto.congr (fun n => (MeasureTheory.integral_map (hXn n).aemeasurable φ.continuous.stronglyMeasurable.aestronglyMeasurable).symm)
      apply Tendsto.congr (fun n => (MeasureTheory.integral_map (aemeasurable_dotProduct (hXn n) t) (continuous_exp_ofReal_mul_I.stronglyMeasurable.aestronglyMeasurable)))
      exact integralConv
    exact φ.continuous.stronglyMeasurable.aestronglyMeasurable


lemma rv_tendsto_if_charFun_tendsto (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)):
  (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t) atTop (𝓝 (charFun (Q.map hX.aemeasurable) t))) → Tendsto (fun n ↦ P.map (hXn n).aemeasurable) atTop (𝓝 (Q.map hX.aemeasurable)) :=
  by
    intro h
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr h

theorem cramerWold (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)) :
  (∀ t : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => P.map (aemeasurable_dotProduct (hXn n) t)) atTop (𝓝 (Q.map (aemeasurable_dotProduct' hX t)))) → (Tendsto (fun n : ℕ => P.map (hXn n).aemeasurable) atTop (𝓝 (Q.map hX.aemeasurable)))
  := by
  intro h
  exact (rv_tendsto_if_charFun_tendsto hX hXn) ((charFun_tendsto_if_inner_tendsto hX hXn) (h))

#min_imports
--#lint unusedHavesSuffices
