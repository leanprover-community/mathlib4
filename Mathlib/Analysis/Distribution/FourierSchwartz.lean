/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Fourier transform on Schwarz functions

This file will construct the Fourier transform as a continuous linear map acting on Schwarz
functions.

For now, it only contains the fact that the Fourier transform of a Schwartz function is
differentiable, with an explicit derivative given by a Fourier transform. See
`SchwartzMap.hasFDerivAt_fourier`.
-/

open Real Complex MeasureTheory Filter TopologicalSpace SchwartzSpace SchwartzMap MeasureTheory
  MeasureTheory.Measure FiniteDimensional VectorFourier

noncomputable section

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (L : D →L[ℝ] E →L[ℝ] ℝ)

/-- Multiplication by a linear map on Schwartz space: for `f : D → V` a Schwartz function and `L` a
bilinear map from `D × E` to `ℝ`, we define a new Schwartz function on `D` taking values in the
space of linear maps from `E` to `V`, given by
`(VectorFourier.mul_L_schwartz L f) (v) = -(2 * π * I) • L (v, ⬝) • f v`.
The point of this definition is that the derivative of the Fourier transform of `f` is the
Fourier transform of `VectorFourier.mul_L_schwartz L f`. -/
def VectorFourier.mul_L_schwartz : 𝓢(D, V) →L[ℝ] 𝓢(D, E →L[ℝ] V) :=
  -(2 * π * I) • (bilinLeftCLM (ContinuousLinearMap.smulRightL ℝ E V).flip L.hasTemperateGrowth)

lemma VectorFourier.mul_L_schwartz_apply (f : 𝓢(D, V)) (d : D) :
    VectorFourier.mul_L_schwartz L f d = VectorFourier.mul_L L f d := rfl

lemma SchwartzMap.integrable_pow_mul [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D]
    (f : 𝓢(D, V)) {μ : Measure D} (k : ℕ) [IsAddHaarMeasure μ] :
    Integrable (fun x ↦ ‖x‖^k * ‖f x‖) μ := by
  let l := finrank ℝ D + 1 + k
  obtain ⟨C, C_nonneg, hC⟩ : ∃ C, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ l * ‖f x‖ ≤ C := by
    let m : ℕ × ℕ := (l, 0)
    refine ⟨2 ^ m.1 * (Finset.Iic m).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, by positivity,
      fun x ↦ ?_⟩
    simpa using f.one_add_le_sup_seminorm_apply (m := m) (k := l) (n := 0) (𝕜 := ℝ) le_rfl le_rfl x
  have : Integrable (fun x : D => C * (1 + ‖x‖) ^ (-((finrank ℝ D + 1 : ℕ) : ℝ))) μ := by
    apply (integrable_one_add_norm ?_).const_mul
    exact Nat.cast_lt.mpr Nat.le.refl
  apply this.mono ((aestronglyMeasurable_id.norm.pow _).mul f.continuous.aestronglyMeasurable.norm)
    (eventually_of_forall (fun x ↦ ?_))
  conv_rhs => rw [norm_of_nonneg (by positivity), rpow_neg (by positivity), ← div_eq_mul_inv]
  rw [le_div_iff' (by positivity)]
  simp only [id_eq, Pi.mul_apply, Pi.pow_apply, norm_mul, norm_pow, norm_norm, rpow_nat_cast]
  calc
  (1 + ‖x‖) ^ (finrank ℝ D + 1) * (‖x‖ ^ k * ‖f x‖)
    ≤ (1 + ‖x‖) ^ (finrank ℝ D + 1) * ((1 + ‖x‖) ^ k * ‖f x‖) := by gcongr; simp
  _ = (1 + ‖x‖) ^ (finrank ℝ D + 1 + k) * ‖f x‖ := by simp [pow_add]; ring
  _ ≤ C := hC x

lemma SchwartzMap.integrable [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D]
    (f : 𝓢(D, V)) {μ : Measure D} [IsAddHaarMeasure μ] :
    Integrable f μ :=
  (f.integrable_pow_mul (μ := μ) 0).mono f.continuous.aestronglyMeasurable
    (eventually_of_forall (fun x ↦ by simp))

attribute [local instance 200] secondCountableTopologyEither_of_left

/-- The Fourier transform of a Schwartz map `f` has a Fréchet derivative (everywhere in its domain)
and its derivative is the Fourier transform of the Schwartz map `mul_L_schwartz L f`. -/
theorem SchwartzMap.hasFDerivAt_fourier [CompleteSpace V] [MeasurableSpace D] [BorelSpace D]
    {μ : Measure D} [FiniteDimensional ℝ D] [IsAddHaarMeasure μ] (f : 𝓢(D, V)) (w : E) :
    HasFDerivAt (fourierIntegral fourierChar μ L.toLinearMap₂ f)
      (fourierIntegral fourierChar μ L.toLinearMap₂ (mul_L_schwartz L f) w) w :=
  VectorFourier.hasFDerivAt_fourier L f.integrable
    (by simpa using f.integrable_pow_mul (μ := μ) 1) w
