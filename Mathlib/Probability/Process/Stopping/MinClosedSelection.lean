/-
Copyright (c) 2026 Granville Gu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Granville Gu
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Order.MinClosedFamily
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Essential-Infimum Stopping Selection Corollary

This module establishes the stopping time essential-infimum selection corollary
by invoking the generic measure-theoretic selection theorem and composing with
Mathlib's native `MeasureTheory.IsStoppingTime.iInf` on continuous time `ℝ≥0`.

Key architectural principles:
1. **Arbitrary Lower Envelope**: The lower bound `S : Ω → ℝ≥0` is purely a pointwise envelope;
   no measurability or stopping-time condition on `S` is assumed or added.
2. **Native Stopping Types**: Formulated directly using Mathlib's native
   `MeasureTheory.IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))` (defined in namespace
`MeasureTheory`).
3. **Ambient Measurability**: The native `measurable_of_Iic` criterion and
   filtration inclusion apply to the stopping-time events.
4. **Countable Infimum Regularity**: Under `[ℱ.IsRightContinuous]`, native Mathlib
   `MeasureTheory.IsStoppingTime.iInf` directly supplies stopping regularity for the pointwise
limit `τstar`.
-/

@[expose] public section
noncomputable section

namespace ProbabilityTheory

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ℝ≥0 mΩ} {D : Set (Ω → ℝ≥0)} {T : ℝ≥0}

omit [IsFiniteMeasure μ] in
/-- Native ambient measurability of a finite stopping time on continuous time `ℝ≥0`. -/
private theorem measurable_of_isStoppingTime {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0))) : Measurable τ := by
  apply measurable_of_Iic
  intro r
  apply ℱ.le r
  change MeasurableSet[ℱ r] {ω | τ ω ≤ r}
  simpa only [WithTop.coe_le_coe] using hτ r

/-- **Headline Corollary: Essential-Infimum Stopping Selection**.
Given any nonempty family `D` of stopping times on a finite measure space, bounded below
by an arbitrary lower envelope `S` and above by deterministic `T`, closed under pointwise minimum:
1. There exists a decreasing sequence `τseq n ∈ D`.
2. `τseq` is pointwise antitone: `∀ n ω, τseq (n + 1) ω ≤ τseq n ω`.
3. The sequence converges pointwise to `τstar`.
4. Under filtration right-continuity `[ℱ.IsRightContinuous]`, `τstar` is a valid stopping time:
   `IsStoppingTime ℱ (fun ω ↦ (τstar ω : WithTop ℝ≥0))`.
5. Pointwise envelope bounds hold: `∀ ω, S ω ≤ τstar ω` and `∀ ω, τstar ω ≤ T`.
6. Lower bound domination: `∀ σ ∈ D, τstar ≤ᵐ[μ] σ` almost everywhere for each competitor. -/
theorem exists_essential_infimum_stopping_selection
    [ℱ.IsRightContinuous] {S : Ω → ℝ≥0}
    (hD_nonempty : D.Nonempty)
    (hD_stop : ∀ τ ∈ D, IsStoppingTime ℱ (fun ω ↦ (τ ω : WithTop ℝ≥0)))
    (hD_min : ∀ τ₁ ∈ D, ∀ τ₂ ∈ D, (fun ω ↦ min (τ₁ ω) (τ₂ ω)) ∈ D)
    (hD_ge : ∀ τ ∈ D, ∀ ω, S ω ≤ τ ω)
    (hD_le : ∀ τ ∈ D, ∀ ω, τ ω ≤ T) :
    ∃ (τseq : ℕ → Ω → ℝ≥0) (τstar : Ω → ℝ≥0),
      (∀ n, τseq n ∈ D) ∧
      (∀ n ω, τseq (n + 1) ω ≤ τseq n ω) ∧
      (∀ ω, Tendsto (fun n ↦ τseq n ω) atTop (𝓝 (τstar ω))) ∧
      IsStoppingTime ℱ (fun ω ↦ (τstar ω : WithTop ℝ≥0)) ∧
      (∀ ω, S ω ≤ τstar ω) ∧
      (∀ ω, τstar ω ≤ T) ∧
      (∀ σ ∈ D, τstar ≤ᵐ[μ] σ) := by
  have hD_meas : ∀ τ ∈ D, Measurable τ := fun τ hτ ↦
    measurable_of_isStoppingTime (hD_stop τ hτ)
  obtain ⟨τseq, τstar, hseq_mem, hseq_anti, hseq_tendsto, hseq_eq, -, hge, hle, hae⟩ :=
    MeasureTheory.exists_essential_infimum_selection_of_min_closed
      (μ := μ) (D := D) (T := T) (S := S)
      hD_nonempty hD_meas hD_min hD_ge hD_le
  have hstop_n (n : ℕ) : IsStoppingTime ℱ (fun ω ↦ (τseq n ω : WithTop ℝ≥0)) :=
    hD_stop (τseq n) (hseq_mem n)
  have hstop_inf : IsStoppingTime ℱ (fun ω ↦ ⨅ n, (τseq n ω : WithTop ℝ≥0)) :=
    IsStoppingTime.iInf hstop_n
  have hstar_eq (ω : Ω) : (τstar ω : WithTop ℝ≥0) = ⨅ n, (τseq n ω : WithTop ℝ≥0) := by
    rw [hseq_eq ω]
    exact WithTop.coe_iInf (OrderBot.bddBelow _)
  have hstop_star : IsStoppingTime ℱ (fun ω ↦ (τstar ω : WithTop ℝ≥0)) := by
    simpa only [← funext hstar_eq] using hstop_inf
  exact ⟨τseq, τstar, hseq_mem, hseq_anti, hseq_tendsto, hstop_star, hge, hle, hae⟩

end ProbabilityTheory
