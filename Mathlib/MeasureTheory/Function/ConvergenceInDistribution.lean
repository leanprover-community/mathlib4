/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convergence in distribution

We introduce a definition of convergence in distribution of random variables: this is the
weak convergence of the laws of the random variables. In Mathlib terms this is a `Tendsto` in the
`ProbabilityMeasure` type.

## Main definitions

* `TendstoInDistribution X l Z μ` : the sequence of random variables `X n` converges in
  distribution to the random variable `Z` along the filter `l` with respect to the probability
  measure `μ`.

## Main statements

* `TendstoInDistribution.continuous_comp`: **Continuous mapping theorem**.
  If `X n` tends to `Z` in distribution and `g` is continuous, then `g ∘ X n` tends to `g ∘ Z`
  in distribution.
-/

open Filter
open scoped Topology

namespace MeasureTheory

variable {Ω ι E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace E] {X Y : ι → Ω → E} {Z : Ω → E} {l : Filter ι}

section TendstoInDistribution

variable [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Convergence in distribution of random variables.
This is the weak convergence of the laws of the random variables: `Tendsto` in the
`ProbabilityMeasure` type.
In order to avoid carrying proofs of measurability in the definition, we declare the convergence
to be true if any of the functions is not almost everywhere measurable. -/
def TendstoInDistribution (X : ι → Ω → E) (l : Filter ι) (Z : Ω → E) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop :=
  (hX : ∀ i, AEMeasurable (X i) μ) → (hZ : AEMeasurable Z μ) →
    Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX n)⟩) l
      (𝓝 ⟨μ.map Z, Measure.isProbabilityMeasure_map hZ⟩)

lemma tendstoInDistribution_def (hX : ∀ i, AEMeasurable (X i) μ) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution X l Z μ ↔
      Tendsto (β := ProbabilityMeasure E)
        (fun n ↦ ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX n)⟩) l
        (𝓝 ⟨μ.map Z, Measure.isProbabilityMeasure_map hZ⟩) := by
  simp [TendstoInDistribution, hX, hZ]

@[simp]
lemma tendstoInDistribution_of_not_aemeasurable_left (hf : ¬ ∀ i, AEMeasurable (X i) μ) :
    TendstoInDistribution X l Z μ := fun hf' ↦ absurd hf' hf

@[simp]
lemma tendstoInDistribution_of_not_aemeasurable_right (hg : ¬ AEMeasurable Z μ) :
    TendstoInDistribution X l Z μ := fun _ hg' ↦ absurd hg' hg

lemma tendstoInDistribution_const :
    TendstoInDistribution (fun _ ↦ Z) l Z μ := fun _ _ ↦ tendsto_const_nhds

lemma tendstoInDistribution_unique {E : Type*} [TopologicalSpace E] [HasOuterApproxClosed E]
    [MeasurableSpace E] [BorelSpace E] (X : ι → Ω → E) {Z W : Ω → E} [l.NeBot]
    (hX : ∀ i, AEMeasurable (X i) μ) (hZ : AEMeasurable Z μ) (hW : AEMeasurable W μ)
    (h1 : TendstoInDistribution X l Z μ) (h2 : TendstoInDistribution X l W μ) :
    μ.map Z = μ.map W := by
  rw [tendstoInDistribution_def hX (by fun_prop)] at h1 h2
  have h_eq := tendsto_nhds_unique h1 h2
  rw [Subtype.ext_iff] at h_eq
  simpa using h_eq

/-- **Continuous mapping theorem**: if `X n` tends to `Z` in distribution and `g` is continuous,
then `g ∘ X n` tends to `g ∘ Z` in distribution. -/
theorem TendstoInDistribution.continuous_comp {F : Type*} [TopologicalSpace F]
    [MeasurableSpace F] [BorelSpace F] {g : E → F} (hg : Continuous g)
    (h : TendstoInDistribution X l Z μ) (hX : ∀ i, AEMeasurable (X i) μ) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution (fun n ↦ g ∘ X n) l (g ∘ Z) μ := by
  intro hX' hZ'
  specialize h hX hZ
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h ⊢
  intro f
  specialize h (f.compContinuous ⟨g, hg⟩)
  simp only [ProbabilityMeasure.coe_mk, BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk] at h
  simp only [ProbabilityMeasure.coe_mk]
  rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hZ,
    integral_map (by fun_prop) (by fun_prop)]
  convert h with n
  rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop)]
  · simp
  · exact Measurable.aestronglyMeasurable <| by fun_prop

end TendstoInDistribution

end MeasureTheory
