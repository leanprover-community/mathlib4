/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Derivative of the Fourier transform

In this file we compute the Fréchet derivative of `𝓕 f`, where `f` is a function such that both
`f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here `𝓕` is understood as an operator `(V → E) → (W → E)`,
where `V` and `W` are normed `ℝ`-vector spaces and the Fourier transform is taken with respect to a
continuous `ℝ`-bilinear pairing `L : V × W → ℝ`.

We also give a separate lemma for the most common case when `V = W = ℝ` and `L` is the obvious
multiplication map.
-/

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology BigOperators

lemma Real.hasDerivAt_fourierChar (x : ℝ) : HasDerivAt (𝐞 · : ℝ → ℂ) (2 * π * I * 𝐞 x) x := by
  have h1 (y : ℝ) : 𝐞 y = fourier 1 (y : UnitAddCircle) := by
    rw [fourierChar_apply, fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one] using hasDerivAt_fourier 1 1 x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

/-- Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v ↦ (w ↦ -2 * π * I * L (v, w) • f v)`. This is designed so that the Fourier transform of
`fourierSMulRight L f` is the derivative of the Fourier transform of `f`. -/
def fourierSMulRight (v : V) : (W →L[ℝ] E) := -(2 * π * I) • (L v).smulRight (f v)

@[simp] lemma fourierSMulRight_apply (v : V) (w : W) :
    fourierSMulRight L f v w = -(2 * π * I) • L v w • f v := rfl

/-- The `w`-derivative of the Fourier transform integrand. -/
lemma hasFDerivAt_fourierChar_smul (v : V) (w : W) :
    HasFDerivAt (fun w' ↦ 𝐞 (-L v w') • f v) (𝐞 (-L v w) • fourierSMulRight L f v) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext1 w'
  simp_rw [fourierSMulRight, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, real_smul, real_smul, Submonoid.smul_def, smul_eq_mul]
  push_cast
  ring_nf

lemma norm_fourierSMulRight (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
      ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := by
  rw [fourierSMulRight, norm_smul, norm_neg, norm_mul, norm_mul, norm_eq_abs I, abs_I,
    mul_one, norm_eq_abs ((_ : ℝ) : ℂ), Complex.abs_of_nonneg pi_pos.le, norm_eq_abs (2 : ℂ),
    Complex.abs_two, ContinuousLinearMap.norm_smulRight_apply, ← mul_assoc]

lemma norm_fourierSMulRight_le (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
    ‖fourierSMulRight L f v‖ ≤ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := calc
  ‖fourierSMulRight L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ := norm_fourierSMulRight _ _ _
  _ ≤ (2 * π) * (‖L‖ * ‖v‖) * ‖f v‖ := by gcongr; exact L.le_opNorm _
  _ = 2 * π * ‖L‖ * ‖v‖ * ‖f v‖ := by ring

lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierSMulRight
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)] [MeasurableSpace V] [BorelSpace V]
    {L : V →L[ℝ] W →L[ℝ] ℝ} {f : V → E} {μ : Measure V}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun v ↦ fourierSMulRight L f v) μ := by
  apply AEStronglyMeasurable.const_smul'
  have aux0 : Continuous fun p : (W →L[ℝ] ℝ) × E ↦ p.1.smulRight p.2 :=
    (ContinuousLinearMap.smulRightL ℝ W E).continuous₂
  have aux1 : AEStronglyMeasurable (fun v ↦ (L v, f v)) μ :=
    L.continuous.aestronglyMeasurable.prod_mk hf
  exact aux0.comp_aestronglyMeasurable aux1

variable {f}

/-- Main theorem of this section: if both `f` and `x ↦ ‖x‖ * ‖f x‖` are integrable, then the
Fourier transform of `f` has a Fréchet derivative (everywhere in its domain) and its derivative is
the Fourier transform of `smulRight L f`. -/
theorem hasFDerivAt_fourier [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)]
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f)
      (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ (fourierSMulRight L f) w) w := by
  let F : W → V → E := fun w' v ↦ 𝐞 (-L v w') • f v
  let F' : W → V → W →L[ℝ] E := fun w' v ↦ 𝐞 (-L v w') • fourierSMulRight L f v
  let B : V → ℝ := fun v ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (VectorFourier.fourier_integral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ L.toLinearMap₂ p.1 p.2)) w').mp hf
  have h1 : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    eventually_of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h3 : AEStronglyMeasurable (F' w) μ := by
    refine .smul ?_ hf.1.fourierSMulRight
    refine (continuous_fourierChar.comp ?_).aestronglyMeasurable
    exact (L.continuous₂.comp (Continuous.Prod.mk_left w)).neg
  have h4 : (∀ᵐ v ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v) := by
    filter_upwards with v w' _
    rw [norm_circle_smul]
    exact norm_fourierSMulRight_le L f v
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : ∀ᵐ v ∂μ, ∀ w', w' ∈ Metric.ball w 1 → HasFDerivAt (fun x ↦ F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ ↦ hasFDerivAt_fourierChar_smul L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le one_pos h1 (h0 w) h3 h4 h5 h6

/-- The formal multilinear series whose `n`-th term is
`(w₁, ..., wₙ) ↦ (-2Iπ)^n * L v w₁ * ... * L v wₙ • f v`.

This is designed so that the Fourier transform of `v ↦ fourierPowSMulRight L f v n` is the
`n`-th derivative of the Fourier transform of `f`.
-/
def fourierPowSMulRight (f : V → E) (v : V) : FormalMultilinearSeries ℝ W E := fun n ↦
  (- (2 * π * I))^n • ((ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (f v)).compContinuousLinearMap
  (fun _i ↦ L v))

@[simp] lemma fourierPowSMulRight_apply {f : V → E} {v : V} {n : ℕ} {m : Fin n → W} :
    fourierPowSMulRight L f v n m = (- (2 * π * I))^n • (∏ i, L v (m i)) • f v := by
  simp [fourierPowSMulRight]

open ContinuousMultilinearMap

/-- Decomposing `fourierPowSMulRight L f v n` as a composition of continuous bilinear and
multilinear maps, to deduce easily its continuity and differentiability properties. -/
lemma fourierPowSMulRight_eq_comp {f : V → E} {v : V} {n : ℕ} :
    fourierPowSMulRight L f v n = (- (2 * π * I))^n • smulRightL ℝ (fun (_ : Fin n) ↦ W) E
      (compContinuousLinearMapLRight
        (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ) (fun _ ↦ L v))
      (f v) := rfl

lemma continuous_fourierPowSMulRight {f : V → E} (hf : Continuous f) (n : ℕ) :
    Continuous (fun v ↦ fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply Continuous.const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp₂ _ hf
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _i ↦ L.continuous))

lemma contDiff_fourierPowSMulRight {f : V → E} {k : ℕ∞} (hf : ContDiff ℝ k f) (n : ℕ) :
    ContDiff ℝ k (fun v ↦ fourierPowSMulRight L f v n) := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply ContDiff.const_smul
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).isBoundedBilinearMap.contDiff.comp₂ _ hf
  apply (ContinuousMultilinearMap.contDiff _).comp
  exact contDiff_pi.2 (fun _ ↦ L.contDiff)

lemma norm_fourierPowSMulRight_le (f : V → E) (v : V) (n : ℕ) :
    ‖fourierPowSMulRight L f v n‖ ≤ (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound _ (by positivity) (fun m ↦ ?_)
  calc
  ‖fourierPowSMulRight L f v n m‖
    = (2 * π) ^ n * ((∏ x : Fin n, |(L v) (m x)|) * ‖f v‖) := by
      simp [_root_.abs_of_nonneg pi_nonneg, norm_smul]
  _ ≤ (2 * π) ^ n * ((∏ x : Fin n, ‖L‖ * ‖v‖ * ‖m x‖) * ‖f v‖) := by
      gcongr with i _hi
      · exact fun i _hi ↦ abs_nonneg _
      · exact L.le_opNorm₂ v (m i)
  _ = (2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖ * ∏ i : Fin n, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, mul_pow]; ring

variable {L}

attribute [local instance 2000] secondCountableTopologyEither_of_left

variable [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}

lemma _root_.MeasureTheory.AEStronglyMeasurable.fourierPowSMulRight
   {n : ℕ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun v ↦ fourierPowSMulRight L f v n) μ := by
  simp_rw [fourierPowSMulRight_eq_comp]
  apply AEStronglyMeasurable.const_smul'
  apply (smulRightL ℝ (fun (_ : Fin n) ↦ W) E).continuous₂.comp_aestronglyMeasurable₂ _ hf
  apply Continuous.aestronglyMeasurable
  exact Continuous.comp (map_continuous _) (continuous_pi (fun _i ↦ L.continuous))

lemma integrable_fourierPowSMulRight {n : ℕ} (hf : Integrable (fun v ↦ ‖v‖ ^ n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) : Integrable (fun v ↦ fourierPowSMulRight L f v n) μ := by
  refine (hf.const_mul ((2 * π * ‖L‖) ^ n)).mono' h'f.fourierPowSMulRight ?_
  filter_upwards with v
  exact (norm_fourierPowSMulRight_le L f v n).trans (le_of_eq (by ring))

#check ContinuousLinearMap.integral_apply

set_option maxHeartbeats 400000 in
lemma hasFTaylorSeriesUpTo_fourierIntegral {N : ℕ∞}
    (hf : ∀ (n : ℕ), n ≤ N → Integrable (fun v ↦ ‖v‖^n * ‖f v‖) μ)
    (h'f : AEStronglyMeasurable f μ) :
    HasFTaylorSeriesUpTo N (VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂ f)
    (fun w n ↦ VectorFourier.fourierIntegral 𝐞 μ L.toLinearMap₂
      (fun v ↦ fourierPowSMulRight L f v n) w) := by
  by_cases hE : CompleteSpace E; swap
  ·

#exit

  constructor
  · intro w
    simp only [uncurry0_apply, Matrix.zero_empty, fourierIntegral]
    rw [integral_apply]
    · simp only [fourierPowSMulRight, pow_zero, one_smul, smul_apply, compContinuousLinearMap_apply,
        mkPiRing_apply, Finset.univ_eq_empty, Finset.prod_empty]
    · simpa only [ContinuousLinearMap.toLinearMap₂_apply, fourierIntegral_convergent_iff] using
        integrable_fourierPowSMulRight (hf 0 bot_le) h'f
  · intro n hn w
    have I₁ : Integrable (fun v ↦ fourierPowSMulRight L f v n) μ :=
      integrable_fourierPowSMulRight (hf n hn.le) h'f
    have I₂ : Integrable (fun v ↦ ‖v‖ * ‖fourierPowSMulRight L f v n‖) μ := by
      apply ((hf (n+1) (ENat.add_one_le_of_lt hn)).const_mul ((2 * π * ‖L‖) ^ n)).mono'
        (continuous_norm.aestronglyMeasurable.mul h'f.fourierPowSMulRight.norm)
      filter_upwards with v
      simp only [Pi.mul_apply, norm_mul, norm_norm]
      calc
      ‖v‖ * ‖fourierPowSMulRight L f v n‖
        ≤ ‖v‖ * ((2 * π * ‖L‖) ^ n * ‖v‖ ^ n * ‖f v‖) := by
          gcongr; apply norm_fourierPowSMulRight_le
      _ = (2 * π * ‖L‖) ^ n * (‖v‖ ^ (n + 1) * ‖f v‖) := by rw [pow_succ]; ring
    have I₃ : Integrable (fun v ↦ 𝐞 (-L.toLinearMap₂ v w)
        • fourierPowSMulRight L f v (Nat.succ n)) μ := by
      simpa only [ContinuousLinearMap.toLinearMap₂_apply, fourierIntegral_convergent_iff] using
        integrable_fourierPowSMulRight (hf (n + 1) (ENat.add_one_le_of_lt hn)) h'f
    have I₄ : Integrable (fun v ↦ 𝐞 (-L.toLinearMap₂ v w)
        • fourierSMulRight L (fun v ↦ fourierPowSMulRight L f v n) v) μ := by
      simp only [ContinuousLinearMap.toLinearMap₂_apply, fourierIntegral_convergent_iff]
      apply (I₂.const_mul ((2 * π * ‖L‖))).mono' h'f.fourierPowSMulRight.fourierSMulRight
      filter_upwards with v
      exact (norm_fourierSMulRight_le _ _ _).trans (le_of_eq (by ring))
    have E : curryLeft
          (fourierIntegral 𝐞 μ L.toLinearMap₂ (fun v ↦ fourierPowSMulRight L f v (Nat.succ n)) w) =
        fourierIntegral 𝐞 μ L.toLinearMap₂
          (fourierSMulRight L fun v ↦ fourierPowSMulRight L f v n) w := by
      ext w' m
      have B v w' : fourierPowSMulRight L f v (Nat.succ n) (Fin.cons w' m) =
          -(2 * ↑π * Complex.I) • L v w' • (fourierPowSMulRight L f v n) m := by
        simp only [fourierPowSMulRight_apply, pow_succ, neg_mul, Fin.prod_univ_succ, Fin.cons_zero,
          Fin.cons_succ, neg_smul, smul_comm (M := ℝ) (N := ℂ) (α := E), smul_smul]
      simp only [fourierIntegral, curryLeft_apply, integral_apply I₃,
        ContinuousLinearMap.integral_apply I₄, integral_apply (I₄.apply_continuousLinearMap _)]
      simp only [ContinuousLinearMap.toLinearMap₂_apply, smul_apply, B, fourierPowSMulRight_apply,
        neg_smul, smul_neg, ContinuousLinearMap.coe_smul', Pi.smul_apply, fourierSMulRight_apply,
        neg_apply]
    rw [E]
    exact hasFDerivAt_fourier L I₁ I₂ w
  · intro n hn
    apply fourierIntegral_continuous Real.continuous_fourierChar (by apply L.continuous₂)
    exact integrable_fourierPowSMulRight (hf n hn) h'f




section inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [CompleteSpace E]

/-- Notation for the Fourier transform on a real inner product space -/
abbrev integralFourier (f : V → E) (μ : Measure V := by volume_tac) :=
  fourierIntegral 𝐞 μ (innerₛₗ ℝ) f

/-- The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
    `fun v ↦ ((-2 * π * I) • f v) ⊗ (innerSL ℝ v)`. -/
theorem InnerProductSpace.hasFDerivAt_fourier {f : V → E} {μ : Measure V}
    (hf_int : Integrable f μ) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖) μ) (x : V) :
    HasFDerivAt (integralFourier f μ) (integralFourier (smulRight (innerSL ℝ) f) μ x) x := by
  haveI : SecondCountableTopologyEither V (V →L[ℝ] ℝ) :=
    secondCountableTopologyEither_of_left V _ -- for some reason it fails to synthesize this?
  exact VectorFourier.hasFDerivAt_fourier (innerSL ℝ) hf_int hvf_int x

end inner

end VectorFourier

open VectorFourier

lemma hasDerivAt_fourierIntegral [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) (w : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (fun x : ℝ ↦ (-2 * ↑π * I * x) • f x) w) w := by
  have hf'' : Integrable (fun v : ℝ ↦ ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using hf'.norm
  let L := ContinuousLinearMap.mul ℝ ℝ
  have h_int : Integrable fun v ↦ smulRight L f v := by
    suffices Integrable fun v ↦ ContinuousLinearMap.smulRight (L v) (f v) by
      simpa only [smulRight, neg_smul, neg_mul, Pi.smul_apply] using this.smul (-2 * π * I)
    convert ((ContinuousLinearMap.ring_lmap_equiv_self ℝ
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', mul_one,
      ContinuousLinearMap.map_smul]
    exact congr_arg (fun x ↦ v • x) (one_smul ℝ (f v)).symm
  rw [fourier_integral_convergent_iff continuous_fourierChar L.continuous₂ w] at h_int
  convert (hasFDerivAt_fourier L hf hf'' w).hasDerivAt using 1
  erw [ContinuousLinearMap.integral_apply h_int]
  simp_rw [ContinuousLinearMap.smul_apply, smulRight, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, L, ContinuousLinearMap.mul_apply', mul_one,
    ← neg_mul, mul_smul]
  rfl
