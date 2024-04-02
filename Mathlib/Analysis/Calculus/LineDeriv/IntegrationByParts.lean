/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Measure

variable {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

lemma blou [SigmaFinite μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) (μ.prod volume))
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) (μ.prod volume))
    (hfg : Integrable (fun x ↦ B (f x) (g x)) (μ.prod volume))
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x (0, 1)) (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂(μ.prod volume) = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
      with x hf'gx hfg'x  hfgx
    apply integral_bilinear_deriv_right_eq_deriv_left_of_integrable ?_ ?_ hfg'x hf'gx hfgx
    · intro t
      convert (hf (x, t)).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp)
        <;> simp
    · intro t
      convert (hg (x, t)).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t))) (by simp)
        <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]

lemma blou2 [FiniteDimensional ℝ E] {μ : Measure (E × ℝ)} [IsAddHaarMeasure μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x (0, 1)) (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x ↦ B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; apply hf'g.smul_measure.nnreal
  have Hfg' : Integrable (fun x ↦ B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; apply hfg'.smul_measure.nnreal
  have Hfg : Integrable (fun x ↦ B (f x) (g x)) (ν.prod volume) := by
    rw [A]; apply hfg.smul_measure.nnreal
  have : μ = (addHaarScalarFactor μ (ν.prod volume)) • (ν.prod volume) :=
    isAddLeftInvariant_eq_smul _ _
  rw [this]
  simp [blou Hf'g Hfg' Hfg hf hg]

open FiniteDimensional

lemma foo (n : ℕ) : 0 ≤ n := by exact?

set_option maxHeartbeats 500000 in
/-- **Integration by parts for line derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are derivatives
of `f` and `g` in a given direction `v`, then `∫ B f' g = - ∫ B f g'`. -/
lemma fou [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]
    {f f' : E → F} {g g' : E → G} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ) (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x v) (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x v) :
    ∫ x, B (f' x) (g x) ∂μ = - ∫ x, B (f x) (g' x) ∂μ := by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  rcases eq_or_ne v 0 with rfl|hv
  · have Hf' x : f' x = 0 := by
      simpa [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv] using (hf x).lineDeriv.symm
    have Hg' x : g' x = 0 := by
      simpa [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv] using (hg x).lineDeriv.symm
    simp [Hf', Hg']
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank ℝ E
  have : 0 < n := by
    simp [n]
    exact?
  let F := Fin (n - 1) → ℝ
  have : finrank ℝ F = n - 1 := by simp [F]
