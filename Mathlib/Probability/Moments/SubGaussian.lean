/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Sub-Gaussian random variables

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details


TODO: this def forces the mean to be 0.
-/

open MeasureTheory Real

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0} {ε : ℝ}

lemma toReal_prob_le_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {s : Set Ω} :
    (μ s).toReal ≤ 1 := by
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

section Kernel

/-- A random variable is sub-Gaussian with parameter `c` with respect to a kernel `κ` and
a measure `μ` if `μ`-almost surely, for all `t : ℝ`, the moment generating function of `X`
with respect to `κ` is bounded by `exp (c * t ^ 2 / 2)`. -/
structure Kernel.IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  -- todo: this is `AEStronglyMeasurable X (ν ⊗ₘ κ)`
  aestronglyMeasurable : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X'
  hasFiniteIntegral_exp_mul : ∀ᵐ ω' ∂ν, ∀ t : ℝ, HasFiniteIntegral (fun ω ↦ exp (t * X ω)) (κ ω')
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t : ℝ, mgf X (κ ω') t ≤ exp (c * t ^ 2 / 2)

def Kernel.IsSubGaussian (X : Ω → ℝ) (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, Kernel.IsSubGaussianWith X c κ ν

namespace Kernel.IsSubGaussianWith

lemma ae_aestronglyMeasurable (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, AEStronglyMeasurable X (κ ω') := by
  obtain ⟨X', hX', hXX'⟩ := h.aestronglyMeasurable
  filter_upwards [hXX'] with ω' h using ⟨X', hX', h⟩

lemma integrable_exp_mul (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  obtain ⟨X', hX', hXX'⟩ := h.aestronglyMeasurable
  filter_upwards [h.hasFiniteIntegral_exp_mul, hXX'] with ω' h_int hXX' t
  refine ⟨⟨fun ω ↦ exp (t * X' ω), ?_, ?_⟩, h_int t⟩
  · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
  · filter_upwards [hXX'] with ω hω
    rw [hω]

lemma integrableExpSet_eq_univ (h : IsSubGaussianWith X c κ ν) :
    ∀ᵐ ω' ∂ν, integrableExpSet X (κ ω') = Set.univ := by
  filter_upwards [h.integrable_exp_mul] with ω' h_int
  ext t
  simp [h_int t, integrableExpSet]

def mkRat (h_meas : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, HasFiniteIntegral (fun ω ↦ exp (n * X ω)) (κ ω'))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.IsSubGaussianWith X c κ ν where
  aestronglyMeasurable := h_meas
  hasFiniteIntegral_exp_mul := by
    rw [← ae_all_iff] at h_int
    filter_upwards [h_int] with ω' h_int t
    refine (integrable_exp_mul_of_le_of_le ?_ ?_ (Int.floor_le t) (Int.le_ceil t)).2
    · sorry
    · sorry
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    sorry

lemma cgf_le (h : IsSubGaussianWith X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.integrable_exp_mul] with ω' h h_int
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simp only [h0, integral_zero_measure, sub_zero, mgf_zero_measure, log_zero, log_exp]
      positivity
    gcongr
    · exact mgf_pos' h0 (h_int t)
    · exact h t
  _ ≤ c * t ^ 2 / 2 := by rw [log_exp]

lemma measure_ge_le_exp_add [IsFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t →
      ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le, h.integrable_exp_mul] with ω' h1 h2 t ht
  calc ((κ ω') {ω | ε ≤ X ω}).toReal
  _ ≤ exp (-t * ε) * mgf X (κ ω') t :=
    measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteKernel κ] (h : IsSubGaussianWith X c κ ν) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc ((κ ω') {ω | ε ≤ X ω}).toReal
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (- (ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by
    congr
    field_simp
    ring

lemma prob_ge_le [IsMarkovKernel κ] (h : IsSubGaussianWith X c κ ν) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, ((κ ω') {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  by_cases hc0 : c = 0
  · refine ae_of_all _ fun ω' ↦ ?_
    simpa [hc0] using toReal_prob_le_one
  · exact h.measure_ge_le (lt_of_le_of_ne zero_le' (Ne.symm hc0)) hε

section Indep

lemma add_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : IsSubGaussianWith X cX κ ν)
    (hY : IsSubGaussianWith Y cY κ ν) (hindep : IndepFun X Y κ ν) :
    IsSubGaussianWith (X + Y) (cX + cY) κ ν where
  aestronglyMeasurable := by
    obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
    obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
    refine ⟨X' + Y', hX'.add hY', ?_⟩
    filter_upwards [hXX', hYY'] with ω hX hY
    exact hX.add hY
  hasFiniteIntegral_exp_mul := by
    suffices ∀ᵐ ω' ∂ν, ∀ (n : ℕ), HasFiniteIntegral (fun ω ↦ rexp (n * (X + Y) ω)) (κ ω') by
      sorry
    rw [ae_all_iff]
    intro n
    refine (hindep.integrable_exp_mul_add ⟨?_, ?_⟩ ⟨?_, ?_⟩).2
    · obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
      refine ⟨fun ω ↦ exp (n * X' ω), ?_, ?_⟩
      · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
      · filter_upwards [hXX'] with ω' hω'
        filter_upwards [hω'] with ω hω
        rw [hω]
    · filter_upwards [hX.hasFiniteIntegral_exp_mul] with ω hX
      exact hX n
    · obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
      refine ⟨fun ω ↦ exp (n * Y' ω), ?_, ?_⟩
      · exact continuous_exp.comp_stronglyMeasurable (hY'.const_mul _)
      · filter_upwards [hYY'] with ω' hω'
        filter_upwards [hω'] with ω hω
        rw [hω]
    · filter_upwards [hY.hasFiniteIntegral_exp_mul] with ω hY
      exact hY n
  mgf_le := by
    filter_upwards [hX.integrable_exp_mul, hY.integrable_exp_mul, hX.mgf_le, hY.mgf_le,
      IndepFun.ae_indepFun hindep] with ω' hX_int hY_int hX hY hindep t
    calc mgf (X + Y) (κ ω') t
    _ = mgf X (κ ω') t * mgf Y (κ ω') t := by rw [hindep.mgf_add (hX_int t).1 (hY_int t).1]
    _ ≤ exp (cX * t ^ 2 / 2) * exp (cY * t ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX t
      · exact hY t
    _ = exp ((cX + cY) * t ^ 2 / 2) := by
      rw [← exp_add]
      congr
      ring

end Indep

end Kernel.IsSubGaussianWith

end Kernel

structure IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le_exp : ∀ t : ℝ, mgf X μ t ≤ exp (c * t ^ 2 / 2)

def IsSubGaussian (X : Ω → ℝ) (μ : Measure Ω := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, IsSubGaussianWith X c μ

lemma isSubGaussianWith_iff_kernel :
  IsSubGaussianWith X c μ
    ↔ Kernel.IsSubGaussianWith X c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by simpa⟩, fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by simpa using h2⟩⟩

lemma isSubGaussian_iff_kernel :
  IsSubGaussian X μ ↔ Kernel.IsSubGaussian X (Kernel.const Unit μ) (Measure.dirac ()) := by
  simp_rw [IsSubGaussian, Kernel.IsSubGaussian, isSubGaussianWith_iff_kernel]

namespace IsSubGaussianWith

lemma cgf_le (h : IsSubGaussianWith X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.cgf_le t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteMeasure μ] (h : IsSubGaussianWith X c μ) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.measure_ge_le hc hε

lemma prob_ge_le [IsProbabilityMeasure μ] (h : IsSubGaussianWith X c μ) (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.prob_ge_le hε

end IsSubGaussianWith

end ProbabilityTheory
