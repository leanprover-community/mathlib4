/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integration by parts for line derivatives

Let `f, g : E → ℝ` be two differentiable functions on a real vector space endowed with a Haar
measure. Then `∫ f * g' = - ∫ f' * g`, where `f'` and `g'` denote the derivatives of `f` and `g`
in a given direction `v`, provided that `f * g`, `f' * g` and `f * g'` are all integrable.

In this file, we prove this theorem as well as more general versions where the multiplication is
replaced by a general continuous bilinear form, giving versions both for the line derivative and
the Fréchet derivative. These results are derived from the one-dimensional version and a Fubini
argument.

## Main statements

* `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`: integration by parts
  in terms of line derivatives, with `HasLineDerivAt` assumptions and general bilinear form.
* `integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable`: integration by parts
  in terms of Fréchet derivatives, with `HasFDerivAt` assumptions and general bilinear form.
* `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`: integration by parts
  in terms of Fréchet derivatives, written with `fderiv` assumptions and general bilinear form.
* `integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`: integration by parts for scalar
  action, in terms of Fréchet derivatives, written with `fderiv` assumptions.
* `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`: integration by parts for scalar
  multiplication, in terms of Fréchet derivatives, written with `fderiv` assumptions.

## Implementation notes

A standard set of assumptions for integration by parts in a finite-dimensional real vector
space (without boundary term) is that the functions tend to zero at infinity and have integrable
derivatives. In this file, we instead assume that the functions are integrable and have integrable
derivatives. These sets of assumptions are not directly comparable (an integrable function with
integrable derivative does *not* have to tend to zero at infinity). The one we use is geared
towards applications to Fourier transforms.

TODO: prove similar theorems assuming that the functions tend to zero at infinity and have
integrable derivatives.
-/
set_option backward.defeqAttrib.useBackward true

public section

open MeasureTheory Measure Module Topology

variable {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [MeasurableSpace E] {μ : Measure E}

lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 [SigmaFinite μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) (μ.prod volume))
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) (μ.prod volume))
    (hfg : Integrable (fun x ↦ B (f x) (g x)) (μ.prod volume))
    (hf : ∀ x ∈ tsupport g, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂(μ.prod volume) = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := calc
  ∫ x, B (f x) (g' x) ∂(μ.prod volume)
    = ∫ x, (∫ t, B (f (x, t)) (g' (x, t))) ∂μ := integral_prod _ hfg'
  _ = ∫ x, (- ∫ t, B (f' (x, t)) (g (x, t))) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hf'g.prod_right_ae, hfg'.prod_right_ae, hfg.prod_right_ae]
      with x hf'gx hfg'x hfgx
    apply integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable ?_ ?_ hfg'x hf'gx hfgx
    · intro t ht
      have : (x, t) ∈ tsupport g :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) g (by fun_prop) ht
      convert (hf (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
    · intro t ht
      have : (x, t) ∈ tsupport f :=
        tsupport_comp_subset_preimage (f := fun y ↦ (x, y)) f (by fun_prop) ht
      convert (hg (x, t) this).scomp_of_eq t ((hasDerivAt_id t).add (hasDerivAt_const t (-t)))
        (by simp) <;> simp
  _ = - ∫ x, B (f' x) (g x) ∂(μ.prod volume) := by rw [integral_neg, integral_prod _ hf'g]

variable [BorelSpace E]

lemma integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
    [FiniteDimensional ℝ E] {μ : Measure (E × ℝ)} [IsAddHaarMeasure μ]
    {f f' : E × ℝ → F} {g g' : E × ℝ → G} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, HasLineDerivAt ℝ f (f' x) x (0, 1))
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x (0, 1)) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  let ν : Measure E := addHaar
  have A : ν.prod volume = (addHaarScalarFactor (ν.prod volume) μ) • μ :=
    isAddLeftInvariant_eq_smul _ _
  have Hf'g : Integrable (fun x ↦ B (f' x) (g x)) (ν.prod volume) := by
    rw [A]; exact hf'g.smul_measure_nnreal
  have Hfg' : Integrable (fun x ↦ B (f x) (g' x)) (ν.prod volume) := by
    rw [A]; exact hfg'.smul_measure_nnreal
  have Hfg : Integrable (fun x ↦ B (f x) (g x)) (ν.prod volume) := by
    rw [A]; exact hfg.smul_measure_nnreal
  rw [isAddLeftInvariant_eq_smul μ (ν.prod volume)]
  simp [integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux1 Hf'g Hfg' Hfg hf hg]

variable [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]

/-- **Integration by parts for line derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`. -/
theorem integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    {f f' : E → F} {g g' : E → G} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ) (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, HasLineDerivAt ℝ f (f' x) x v)
    (hg : ∀ x ∈ tsupport f, HasLineDerivAt ℝ g (g' x) x v) :
    ∫ x, B (f x) (g' x) ∂μ = - ∫ x, B (f' x) (g x) ∂μ := by
  by_cases hW : CompleteSpace W; swap
  · simp [integral_def, hW]
  rcases eq_or_ne v 0 with rfl | hv
  · have Hf' x : B (f' x) (g x) = 0 := by
      by_cases hx : x ∈ tsupport g
      · simp [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv, (hf x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    have Hg' x : B (f x) (g' x) = 0 := by
      by_cases hx : x ∈ tsupport f
      · simp [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv, (hg x hx).lineDeriv.symm]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    simp [Hf', Hg']
  have : Nontrivial E := nontrivial_iff.2 ⟨v, 0, hv⟩
  let n := finrank ℝ E
  let E' := Fin (n - 1) → ℝ
  obtain ⟨L, hL⟩ : ∃ L : E ≃L[ℝ] (E' × ℝ), L v = (0, 1) := by
    have : finrank ℝ (E' × ℝ) = n := by simpa [this, E'] using Nat.sub_add_cancel finrank_pos
    have L₀ : E ≃L[ℝ] (E' × ℝ) := (ContinuousLinearEquiv.ofFinrankEq this).symm
    obtain ⟨M, hM⟩ : ∃ M : (E' × ℝ) ≃L[ℝ] (E' × ℝ), M (L₀ v) = (0, 1) := by
      apply SeparatingDual.exists_continuousLinearEquiv_apply_eq
      · simpa using hv
      · simp
    exact ⟨L₀.trans M, by simp [hM]⟩
  let ν := Measure.map L μ
  suffices H : ∫ (x : E' × ℝ), (B (f (L.symm x))) (g' (L.symm x)) ∂ν =
      -∫ (x : E' × ℝ), (B (f' (L.symm x))) (g (L.symm x)) ∂ν by
    have : μ = Measure.map L.symm ν := by
      simp [ν, Measure.map_map L.symm.continuous.measurable L.continuous.measurable]
    have hL : IsClosedEmbedding L.symm := L.symm.toHomeomorph.isClosedEmbedding
    simpa [this, hL.integral_map] using H
  have L_emb : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable_aux2
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hf'g
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg'
  · simpa [ν, L_emb.integrable_map_iff, Function.comp_def] using hfg
  · intro x hx
    have : f = (f ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h2x : L.symm x ∈ tsupport g :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage g L.symm.toHomeomorph) x).mp hx
    specialize hf (L.symm x) h2x
    rw [this] at hf
    convert hf.of_comp using 1
    · simp
    · simp [← hL]
  · intro x hx
    have : g = (g ∘ L.symm) ∘ (L : E →ₗ[ℝ] (E' × ℝ)) := by ext y; simp
    have h2x : L.symm x ∈ tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f L.symm.toHomeomorph) x).mp hx
    specialize hg (L.symm x) h2x
    rw [this] at hg
    convert hg.of_comp using 1
    · simp
    · simp [← hL]

/-- **Integration by parts for Fréchet derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`. -/
theorem integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    {f : E → F} {f' : E → (E →L[ℝ] F)}
    {g : E → G} {g' : E → (E →L[ℝ] G)} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x v) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (g' x v)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, HasFDerivAt f (f' x) x)
    (hg : ∀ x ∈ tsupport f, HasFDerivAt g (g' x) x) :
    ∫ x, B (f x) (g' x v) ∂μ = - ∫ x, B (f' x v) (g x) ∂μ :=
  integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasLineDerivAt v) (hg · · |>.hasLineDerivAt v)

/-- **Integration by parts for Fréchet derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are the derivatives
of `f` and `g` in a given direction `v`, then `∫ B f g' = - ∫ B f' g`. -/
theorem integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    {f : E → F} {g : E → G} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (fderiv ℝ f x v) (g x)) μ)
    (hfg' : Integrable (fun x ↦ B (f x) (fderiv ℝ g x v)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, B (f x) (fderiv ℝ g x v) ∂μ = - ∫ x, B (fderiv ℝ f x v) (g x) ∂μ :=
  integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable hf'g hfg' hfg
    (hf · · |>.hasFDerivAt) (hg · · |>.hasFDerivAt)

variable {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 G] [IsScalarTower ℝ 𝕜 G]

/-- **Integration by parts for Fréchet derivatives**
Version with a scalar function: `∫ f • g' = - ∫ f' • g` when `f • g'` and `f' • g` and `f • g`
are integrable, where `f'` and `g'` are the derivatives of `f` and `g` in a given direction `v`. -/
theorem integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    {f : E → 𝕜} {g : E → G} {v : E}
    (hf'g : Integrable (fun x ↦ fderiv ℝ f x v • g x) μ)
    (hfg' : Integrable (fun x ↦ f x • fderiv ℝ g x v) μ)
    (hfg : Integrable (fun x ↦ f x • g x) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, f x • fderiv ℝ g x v ∂μ = - ∫ x, fderiv ℝ f x v • g x ∂μ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ 𝕜) hf'g hfg' hfg hf hg

/-- **Integration by parts for Fréchet derivatives**
Version with two scalar functions: `∫ f * g' = - ∫ f' * g` when `f * g'` and `f' * g` and `f * g`
are integrable, where `f'` and `g'` are the derivatives of `f` and `g` in a given direction `v`. -/
theorem integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    {f : E → 𝕜} {g : E → 𝕜} {v : E}
    (hf'g : Integrable (fun x ↦ fderiv ℝ f x v * g x) μ)
    (hfg' : Integrable (fun x ↦ f x * fderiv ℝ g x v) μ)
    (hfg : Integrable (fun x ↦ f x * g x) μ)
    (hf : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x) :
    ∫ x, f x * fderiv ℝ g x v ∂μ = - ∫ x, fderiv ℝ f x v * g x ∂μ :=
  integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ 𝕜) hf'g hfg' hfg hf hg
