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

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0} {ε : ℝ}

lemma toReal_prob_le_one {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {s : Set Ω} :
    (μ s).toReal ≤ 1 := by
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one

lemma continuous_mgf (h : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) μ) :
    Continuous (fun t ↦ mgf X μ t) := by
  rw [continuous_iff_continuousOn_univ]
  convert continuousOn_mgf
  ext t
  simp only [Set.mem_univ, true_iff]
  rw [mem_interior]
  refine ⟨Set.Ioo (t - 1) (t + 1), fun x hx ↦ ?_, isOpen_Ioo, by simp⟩
  exact integrable_exp_mul_of_le_of_le (h (t - 1)) (h (t + 1)) hx.1.le hx.2.le

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

lemma hasFiniteIntegral_exp_mul_of_int
    (h_meas : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, HasFiniteIntegral (fun ω ↦ exp (n * X ω)) (κ ω')) :
    ∀ᵐ ω' ∂ν, ∀ t, HasFiniteIntegral (fun ω ↦ rexp (t * X ω)) (κ ω') := by
  rw [← ae_all_iff] at h_int
  obtain ⟨X', hX', hXX'⟩ := h_meas
  filter_upwards [h_int, hXX'] with ω' h_int hXX' t
  refine (integrable_exp_mul_of_le_of_le ?_ ?_ (Int.floor_le t) (Int.le_ceil t)).2
  · refine ⟨⟨fun ω ↦ exp (⌊t⌋ * X' ω), ?_, ?_⟩, h_int _⟩
    · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
    · filter_upwards [hXX'] with ω hω
      rw [hω]
  · refine ⟨⟨fun ω ↦ exp (⌈t⌉ * X' ω), ?_, ?_⟩, h_int _⟩
    · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
    · filter_upwards [hXX'] with ω hω
      rw [hω]

open Filter in
def mkRat (h_meas : ∃ X', StronglyMeasurable X' ∧ ∀ᵐ ω' ∂ν, X =ᵐ[κ ω'] X')
    (h_int : ∀ n : ℤ, ∀ᵐ ω' ∂ν, HasFiniteIntegral (fun ω ↦ exp (n * X ω)) (κ ω'))
    (h_mgf : ∀ q : ℚ, ∀ᵐ ω' ∂ν, mgf X (κ ω') q ≤ exp (c * q ^ 2 / 2)) :
    Kernel.IsSubGaussianWith X c κ ν where
  aestronglyMeasurable := h_meas
  hasFiniteIntegral_exp_mul := hasFiniteIntegral_exp_mul_of_int h_meas h_int
  mgf_le := by
    rw [← ae_all_iff] at h_mgf
    let ⟨X', hX', hXX'⟩ := h_meas
    filter_upwards [h_mgf, hasFiniteIntegral_exp_mul_of_int h_meas h_int, hXX']
      with ω' h_mgf h_int hXX' t
    refine Rat.denseRange_cast.induction_on t ?_ h_mgf
    refine isClosed_le ?_ (by fun_prop)
    refine continuous_mgf fun u ↦ ?_
    refine ⟨⟨fun ω ↦ exp (u * X' ω), ?_, ?_⟩, h_int u⟩
    · exact continuous_exp.comp_stronglyMeasurable (hX'.const_mul _)
    · filter_upwards [hXX'] with ω hω
      rw [hω]

lemma cgf_le (h : IsSubGaussianWith X c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, cgf X (κ ω') t ≤ c * t ^ 2 / 2 := by
  filter_upwards [h.mgf_le, h.integrable_exp_mul] with ω' h h_int
  calc cgf X (κ ω') t
  _ = log (mgf X (κ ω') t) := rfl
  _ ≤ log (exp (c * t ^ 2 / 2)) := by
    by_cases h0 : κ ω' = 0
    · simp only [h0, mgf_zero_measure, Pi.zero_apply, log_zero, log_exp]
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
    IsSubGaussianWith (X + Y) (cX + cY) κ ν := by
  obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
  obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
  have h_expX (t : ℝ) : ∃ X', StronglyMeasurable X'
      ∧ ∀ᵐ ω' ∂ν, (fun ω ↦ exp (t * X ω)) =ᶠ[ae (κ ω')] X' := by
    obtain ⟨X', hX', hXX'⟩ := hX.aestronglyMeasurable
    refine ⟨fun ω ↦ exp (t * X' ω), continuous_exp.comp_stronglyMeasurable (hX'.const_mul _), ?_⟩
    filter_upwards [hXX'] with ω' hω'
    filter_upwards [hω'] with ω hω
    rw [hω]
  have h_expY (t : ℝ) : ∃ Y', StronglyMeasurable Y'
      ∧ ∀ᵐ ω' ∂ν, (fun ω ↦ exp (t * Y ω)) =ᶠ[ae (κ ω')] Y' := by
    obtain ⟨Y', hY', hYY'⟩ := hY.aestronglyMeasurable
    refine ⟨fun ω ↦ exp (t * Y' ω), continuous_exp.comp_stronglyMeasurable (hY'.const_mul _), ?_⟩
    filter_upwards [hYY'] with ω' hω'
    filter_upwards [hω'] with ω hω
    rw [hω]
  refine mkRat ?_ ?_ ?_
  · refine ⟨X' + Y', hX'.add hY', ?_⟩
    filter_upwards [hXX', hYY'] with ω hX hY
    exact hX.add hY
  · intro n
    have h := hindep.integrable_exp_mul_add (h_expX n) (h_expY n)
    filter_upwards [h.2, hX.integrable_exp_mul, hY.integrable_exp_mul] with ω' h hX hY
    specialize h (hX n) (hY n)
    exact h.2
  · intro q
    have h := hindep.mgf_add (h_expX q) (h_expY q)
    filter_upwards [h, hX.mgf_le, hY.mgf_le] with ω' h hX hY
    calc mgf (X + Y) (κ ω') q
    _ = mgf X (κ ω') q * mgf Y (κ ω') q := by rw [h]
    _ ≤ exp (cX * q ^ 2 / 2) * exp (cY * q ^ 2 / 2) := by
      gcongr
      · exact mgf_nonneg
      · exact hX q
      · exact hY q
    _ = exp ((cX + cY) * q ^ 2 / 2) := by
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
    ↔ Kernel.IsSubGaussianWith X c (Kernel.const Unit μ) (Measure.dirac ()) := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun ⟨h1, h2, h3⟩ ↦ ?_⟩
  · constructor
    · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
      exact (aemeasurable_of_aemeasurable_exp_mul one_ne_zero
        (h1 1).1.aemeasurable).aestronglyMeasurable
    · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure]
      exact fun t ↦ (h1 t).2
    · simpa
  · constructor
    · simp only [Kernel.const_apply, ae_dirac_eq, Filter.eventually_pure] at h1 h2
      obtain ⟨X', hX', hXX'⟩ := h1
      refine fun t ↦ ⟨⟨fun ω ↦ exp (t * X' ω),
        continuous_exp.comp_stronglyMeasurable (hX'.const_mul t), ?_⟩, h2 t⟩
      filter_upwards [hXX'] with ω hω
      rw [hω]
    · simpa using h3

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

lemma add_indepFun {Y : Ω → ℝ} {cX cY : ℝ≥0} (hX : IsSubGaussianWith X cX μ)
    (hY : IsSubGaussianWith Y cY μ) (hindep : IndepFun X Y μ) :
    IsSubGaussianWith (X + Y) (cX + cY) μ := by
  rw [isSubGaussianWith_iff_kernel] at hX hY ⊢
  simpa using hX.add_indepFun hY hindep

end IsSubGaussianWith

end ProbabilityTheory
