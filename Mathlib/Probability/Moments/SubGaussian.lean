/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Sub-Gaussian random variables

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open MeasureTheory Real

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {c : ℝ≥0}

section Kernel

/-- A random variable is sub-Gaussian with parameter `c` with respect to a kernel `κ` and
a measure `μ` if `μ`-almost surely, for all `t : ℝ`, the moment generating function of
`X - (κ ω')[X]` with respect to `κ` is bounded by `exp (c * t ^ 2 / 2)`.
We center `X` to avoid imposing `(κ ω')[X] = 0`. -/
structure Kernel.IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ᵐ ω' ∂ν, ∀ t : ℝ, Integrable (fun ω ↦ exp (t * (X ω - (κ ω')[X]))) (κ ω')
  mgf_le_exp : ∀ᵐ ω' ∂ν, ∀ t : ℝ, mgf (fun ω ↦ X ω - (κ ω')[X]) (κ ω') t ≤ exp (c * t ^ 2 / 2)

def Kernel.IsSubGaussian (X : Ω → ℝ) (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop :=
  ∃ c : ℝ≥0, Kernel.IsSubGaussianWith X c κ ν

namespace Kernel.IsSubGaussianWith

lemma measure_ge_le_exp_add [IsFiniteKernel κ] (h : Kernel.IsSubGaussianWith X c κ ν) (ε : ℝ) :
    ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t →
      ((κ ω') {ω | ε ≤ X ω - (κ ω')[X]}).toReal ≤ exp (- t * ε + c * t ^ 2 / 2) := by
  filter_upwards [h.mgf_le_exp, h.integrable_exp_mul] with ω' h1 h2 t ht
  calc ((κ ω') {ω | ε ≤ X ω - (κ ω')[X]}).toReal
  _ ≤ exp (-t * ε) * mgf (fun ω ↦ X ω - (κ ω')[X]) (κ ω') t :=
    measure_ge_le_exp_mul_mgf ε ht (h2 t)
  _ ≤ exp (-t * ε + c * t ^ 2 / 2) := by
    rw [exp_add]
    gcongr
    exact h1 t

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteKernel κ] (h : Kernel.IsSubGaussianWith X c κ ν) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    ∀ᵐ ω' ∂ν, ((κ ω') {ω | ε ≤ X ω - (κ ω')[X]}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  filter_upwards [measure_ge_le_exp_add h ε] with ω' h
  calc ((κ ω') {ω | ε ≤ X ω - (κ ω')[X]}).toReal
  -- choose the minimizer of the r.h.s. of `h` for `t ≥ 0`. That is, `t = ε / c`.
  _ ≤ exp (- (ε / c) * ε + c * (ε / c) ^ 2 / 2) := h (ε / c) (by positivity)
  _ = exp (- ε ^ 2 / (2 * c)) := by
    congr
    field_simp
    ring

end Kernel.IsSubGaussianWith

end Kernel

structure IsSubGaussianWith (X : Ω → ℝ) (c : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * (X ω - μ[X]))) μ
  mgf_le_exp : ∀ t : ℝ, mgf (fun ω ↦ X ω - μ[X]) μ t ≤ exp (c * t ^ 2 / 2)

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

/-- Chernoff bound on the right tail of a sub-Gaussian random variable. -/
lemma measure_ge_le [IsFiniteMeasure μ] (h : IsSubGaussianWith X c μ) {ε : ℝ}
    (hc : 0 < c) (hε : 0 ≤ ε) :
    (μ {ω | ε ≤ X ω - μ[X]}).toReal ≤ exp (- ε ^ 2 / (2 * c)) := by
  rw [isSubGaussianWith_iff_kernel] at h
  simpa using h.measure_ge_le hc hε

end IsSubGaussianWith

end ProbabilityTheory
