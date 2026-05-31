/-
Copyright (c) 2026 Rob Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Sneiderman
-/
module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-! # Ville's inequality (maximal inequality for nonnegative supermartingales)

This file proves **Ville's inequality**: the time-uniform maximal inequality for nonnegative
supermartingales. It is the exact supermartingale dual of Doob's maximal inequality for
nonnegative submartingales (`MeasureTheory.maximal_ineq`).

Given a nonnegative supermartingale `f` and `ε : ℝ≥0`, the anytime (countable-horizon) form is
`ε * μ {ω | ∃ n, ε ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0])`, and the finite-horizon form is
`ε * μ {ω | ε ≤ f* n} ≤ ENNReal.ofReal (μ[f 0])` where `f* n ω = max_{k ≤ n} f k ω`.

Note that the dual is **not** obtained by negating Doob's inequality: negating a nonnegative
supermartingale produces a submartingale that is no longer nonnegative, so `maximal_ineq` does not
transfer. Instead the proof goes directly through optional stopping (`Supermartingale.neg`,
`Submartingale.expected_stoppedValue_mono`) and a hitting time, then passes to the countable
horizon via `tendsto_measure_iUnion_atTop`.

The probability-normalized corollaries `ville_maximal_ineq_of_integral_le_one`,
`ville_maximal_ineq_exists_le_of_integral_le_one`, and `ville_inequality_of_integral_le_one`
are the forms used in sequential analysis: if `μ[f 0] ≤ 1` then the level `α⁻¹` crossing
event has measure at most `α`. These are the inequalities behind anytime-valid testing,
e-processes, and confidence sequences.

### Main results

* `MeasureTheory.Supermartingale.expected_stoppedValue_le_start`: for a supermartingale, the
  expected stopped value at a bounded stopping time is at most the initial expectation.
* `MeasureTheory.ville_maximal_ineq`: finite-horizon Ville's inequality.
* `MeasureTheory.ville_maximal_ineq_exists_le`: finite-horizon Ville's inequality with the
  crossing event stated as `∃ k ≤ n`.
* `MeasureTheory.ville_maximal_ineq_of_integral_le_one`,
  `MeasureTheory.ville_maximal_ineq_exists_le_of_integral_le_one`,
  `MeasureTheory.ville_inequality_of_integral_le_one`: the probability-normalized `α` forms.
* `MeasureTheory.ville_inequality`: anytime Ville's inequality.

### References

* [J. Ville, *Étude critique de la notion de collectif*][ville_1939].
* Doob's submartingale maximal inequality: `MeasureTheory.maximal_ineq`.
-/

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

open ProbabilityTheory Finset

namespace MeasureTheory

public section

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {τ : Ω → ℕ∞}

/-- Optional-stopping consequence for supermartingales: the expected stopped value at a bounded
stopping time is bounded by the initial expectation. This is the supermartingale counterpart of
`MeasureTheory.Submartingale.expected_stoppedValue_mono` specialized to a constant lower time. -/
theorem Supermartingale.expected_stoppedValue_le_start
    [SigmaFiniteFiltration μ 𝒢]
    (hf : Supermartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    μ[stoppedValue f τ] ≤ μ[f 0] := by
  have hmono :=
    (Supermartingale.neg hf).expected_stoppedValue_mono
      (isStoppingTime_const 𝒢 0) hτ (fun _ => bot_le) hbdd
  rw [stoppedValue_const] at hmono
  change μ[fun ω => -f 0 ω] ≤ μ[fun ω => -stoppedValue f τ ω] at hmono
  rw [integral_neg, integral_neg] at hmono
  linarith

/-- Hitting-time step for finite-time Ville: on the maximal-crossing event, the
threshold times the event mass is bounded by the integral of the value at the
hitting time. Supermartingale analogue of
`MeasureTheory.smul_le_stoppedValue_hittingBtwn`. -/
private theorem smul_le_stoppedValue_hittingBtwn_of_supermartingale [IsFiniteMeasure μ]
    (hsuper : Supermartingale f 𝒢 μ) {ε : ℝ≥0} (n : ℕ) :
    ε • μ {ω |
      (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal
      (∫ ω in {ω |
          (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
        stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω ∂μ) := by
  have hhit :
      ∀ ω,
        ((ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) →
          (ε : ℝ) ≤
            stoppedValue f (fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_setOf_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ => (hsuper.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) hhit (Integrable.integrableOn
        (integrable_stoppedValue ℕ
          (hsuper.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          hsuper.integrable (N := n)
          (fun ω => by
            exact WithTop.coe_le_coe.2
              (hittingBtwn_le (u := f) (s := {y : ℝ | ε ≤ y}) (n := 0) (m := n) ω))))
  rw [ENNReal.le_ofReal_iff_toReal_le, ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

-- The following coercion-heavy stopped-value comparison is transparency-sensitive in Lean 4.31.
set_option backward.isDefEq.respectTransparency false in
/-- **Ville's inequality (finite horizon)**: for a nonnegative supermartingale `f` and `ε : ℝ≥0`,
`ε * μ {ω | ε ≤ max_{k ≤ n} f k ω} ≤ ENNReal.ofReal (μ[f 0])`. This is the supermartingale dual of
Doob's `MeasureTheory.maximal_ineq`. -/
theorem ville_maximal_ineq [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0} (n : ℕ) :
    ε * μ {ω |
      (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    ENNReal.ofReal (μ[f 0]) := by
  let τ : Ω → ℕ∞ := fun ω ↦ (hittingBtwn f {y : ℝ | ε ≤ y} 0 n ω : ℕ)
  let event : Set Ω :=
    {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}
  have hτ : IsStoppingTime 𝒢 τ :=
    hsuper.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hbdd : ∀ ω, τ ω ≤ n := by
    intro ω
    dsimp [τ]
    exact_mod_cast
      (hittingBtwn_le (u := f) (s := {y : ℝ | ε ≤ y}) (n := 0) (m := n) ω)
  have hstop_int : Integrable (stoppedValue f τ) μ :=
    integrable_stoppedValue ℕ hτ hsuper.integrable hbdd
  have hstop_nonneg : 0 ≤ᵐ[μ] stoppedValue f τ :=
    Filter.Eventually.of_forall fun ω => hnonneg _ _
  calc
    ε * μ event
        ≤ ENNReal.ofReal (∫ ω in event, stoppedValue f τ ω ∂μ) := by
          simpa [event, τ, smul_eq_mul] using
            smul_le_stoppedValue_hittingBtwn_of_supermartingale
              (μ := μ) (𝒢 := 𝒢) (f := f) hsuper (ε := ε) n
    _ ≤ ENNReal.ofReal (μ[stoppedValue f τ]) := by
          exact ENNReal.ofReal_le_ofReal
            (setIntegral_le_integral hstop_int hstop_nonneg)
    _ ≤ ENNReal.ofReal (μ[f 0]) := by
          exact ENNReal.ofReal_le_ofReal
            (Supermartingale.expected_stoppedValue_le_start hsuper hτ hbdd)

/-- Finite-horizon Ville's inequality with the crossing event written as `∃ k ≤ n`. This is
equivalent to `ville_maximal_ineq` and is often the more convenient downstream statement. -/
theorem ville_maximal_ineq_exists_le [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0} (n : ℕ) :
    ε * μ {ω | ∃ k : ℕ, k ≤ n ∧ (ε : ℝ) ≤ f k ω} ≤
    ENNReal.ofReal (μ[f 0]) := by
  have heq :
      {ω | ∃ k : ℕ, k ≤ n ∧ (ε : ℝ) ≤ f k ω} =
      {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} := by
    ext ω
    constructor
    · rintro ⟨k, hk, hεk⟩
      exact Finset.le_sup'_of_le
        (s := range (n + 1)) (f := fun j => f j ω) (a := (ε : ℝ)) (b := k)
        (mem_range.mpr (Nat.lt_succ_of_le hk)) hεk
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [Finset.le_sup'_iff] at h
      rcases h with ⟨k, hk, hεk⟩
      exact ⟨k, Nat.le_of_lt_succ (mem_range.mp hk), hεk⟩
  rw [heq]
  exact ville_maximal_ineq (μ := μ) (𝒢 := 𝒢) (f := f) hsuper hnonneg (ε := ε) n

/-- Probability-normalized finite-horizon Ville inequality. If a nonnegative supermartingale starts
with expectation at most one, then the finite-horizon level `α⁻¹` crossing event has measure at
most `α`. -/
theorem ville_maximal_ineq_of_integral_le_one
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (hstart : μ[f 0] ≤ 1) {α : NNReal} (hα : 0 < α) (n : ℕ) :
    μ {ω | ((α⁻¹ : NNReal) : ℝ) ≤
      (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} ≤
    (α : ℝ≥0∞) := by
  let bad : Set Ω := {ω | ((α⁻¹ : NNReal) : ℝ) ≤
    (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}
  let ε : NNReal := α⁻¹
  have hville :
      ε * μ bad ≤ ENNReal.ofReal (μ[f 0]) := by
    simpa [bad, ε] using
      ville_maximal_ineq (μ := μ) (𝒢 := 𝒢) (f := f)
        hsuper hnonneg (ε := ε) n
  have hstart_enn : ENNReal.ofReal (μ[f 0]) ≤ 1 := by
    simpa using (ENNReal.ofReal_le_ofReal hstart)
  have hscaled : (α⁻¹ : NNReal) * μ bad ≤ 1 := hville.trans hstart_enn
  have hmul : (α : ℝ≥0∞) * ((α⁻¹ : NNReal) * μ bad) ≤ (α : ℝ≥0∞) * 1 := by gcongr
  have hα_ne_zero : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
  have hcoe_inv : ((α⁻¹ : NNReal) : ℝ≥0∞) = (α : ℝ≥0∞)⁻¹ := ENNReal.coe_inv hα.ne'
  have hcancel :
      (α : ℝ≥0∞) * ((α⁻¹ : NNReal) * μ bad) = μ bad := by
    rw [hcoe_inv]
    exact ENNReal.mul_inv_cancel_left (a := (α : ℝ≥0∞)) (b := μ bad)
      hα_ne_zero ENNReal.coe_ne_top
  change μ bad ≤ (α : ℝ≥0∞)
  rw [← hcancel]
  simpa using hmul

/-- Probability-normalized finite-horizon Ville inequality with the crossing event written as
`∃ k ≤ n`. -/
theorem ville_maximal_ineq_exists_le_of_integral_le_one
    [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (hstart : μ[f 0] ≤ 1) {α : NNReal} (hα : 0 < α) (n : ℕ) :
    μ {ω | ∃ k : ℕ, k ≤ n ∧ ((α⁻¹ : NNReal) : ℝ) ≤ f k ω} ≤
    (α : ℝ≥0∞) := by
  have heq :
      {ω | ∃ k : ℕ, k ≤ n ∧ ((α⁻¹ : NNReal) : ℝ) ≤ f k ω} =
      {ω | ((α⁻¹ : NNReal) : ℝ) ≤
        (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} := by
    ext ω
    constructor
    · rintro ⟨k, hk, hαk⟩
      exact Finset.le_sup'_of_le
        (s := range (n + 1)) (f := fun j => f j ω)
        (a := (((α⁻¹ : NNReal) : ℝ))) (b := k)
        (mem_range.mpr (Nat.lt_succ_of_le hk)) hαk
    · intro h
      rw [Set.mem_setOf_eq] at h
      rw [Finset.le_sup'_iff] at h
      rcases h with ⟨k, hk, hαk⟩
      exact ⟨k, Nat.le_of_lt_succ (mem_range.mp hk), hαk⟩
  rw [heq]
  exact ville_maximal_ineq_of_integral_le_one
    (μ := μ) (𝒢 := 𝒢) (f := f) hsuper hnonneg hstart hα n

/-- Countable-horizon Ville inequality, stated over the increasing union of finite-horizon
crossing events. -/
private theorem ville_inequality_iUnion [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0} :
    ε * μ (⋃ n : ℕ,
      {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}) ≤
    ENNReal.ofReal (μ[f 0]) := by
  let A : ℕ → Set Ω := fun n =>
    {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}
  have hmono : Monotone A := by
    intro n m hnm ω hω
    dsimp [A] at hω ⊢
    exact hω.trans
      (Finset.sup'_mono (f := fun k => f k ω)
        (Finset.range_mono (Nat.succ_le_succ hnm)) nonempty_range_add_one)
  have htendsto :
      Filter.Tendsto (fun n => (ε : ℝ≥0∞) * μ (A n)) Filter.atTop
        (𝓝 ((ε : ℝ≥0∞) * μ (⋃ n, A n))) :=
    ENNReal.Tendsto.const_mul (tendsto_measure_iUnion_atTop (μ := μ) hmono)
      (Or.inr ENNReal.coe_ne_top)
  have hle : ∀ n, (ε : ℝ≥0∞) * μ (A n) ≤ ENNReal.ofReal (μ[f 0]) := by
    intro n
    exact ville_maximal_ineq (μ := μ) (𝒢 := 𝒢) (f := f) hsuper hnonneg (ε := ε) n
  simpa [A] using le_of_tendsto' htendsto hle

/-- **Ville's inequality (anytime form)**: for a nonnegative supermartingale `f` and `ε : ℝ≥0`,
`ε * μ {ω | ∃ n, ε ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0])`. The time-uniform crossing bound behind
anytime-valid sequential inference. -/
theorem ville_inequality [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : ℝ≥0} :
    ε * μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ f n ω} ≤ ENNReal.ofReal (μ[f 0]) := by
  have heq :
      (⋃ n : ℕ,
        {ω | (ε : ℝ) ≤ (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}) =
      {ω | ∃ n : ℕ, (ε : ℝ) ≤ f n ω} := by
    ext ω
    constructor
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
      rw [Set.mem_setOf_eq] at hn
      rw [Finset.le_sup'_iff] at hn
      rcases hn with ⟨k, _hk, hεk⟩
      exact ⟨k, hεk⟩
    · rintro ⟨k, hεk⟩
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      exact Finset.le_sup'_of_le
        (s := range (k + 1)) (f := fun j => f j ω) (a := (ε : ℝ)) (b := k)
        (mem_range.mpr (Nat.lt_succ_self k)) hεk
  rw [← heq]
  exact ville_inequality_iUnion (μ := μ) (𝒢 := 𝒢) (f := f) hsuper hnonneg (ε := ε)

/-- Probability-normalized anytime Ville inequality. If a nonnegative supermartingale starts with
expectation at most one, then the level `α⁻¹` anytime crossing event has measure at most `α`. -/
theorem ville_inequality_of_integral_le_one [IsFiniteMeasure μ] [SigmaFiniteFiltration μ 𝒢]
    (hsuper : Supermartingale f 𝒢 μ) (hnonneg : 0 ≤ f)
    (hstart : μ[f 0] ≤ 1) {α : NNReal} (hα : 0 < α) :
    μ {ω | ∃ n : ℕ, ((α⁻¹ : NNReal) : ℝ) ≤ f n ω} ≤ (α : ℝ≥0∞) := by
  let bad : Set Ω := {ω | ∃ n : ℕ, ((α⁻¹ : NNReal) : ℝ) ≤ f n ω}
  let ε : NNReal := α⁻¹
  have hville :
      ε * μ bad ≤ ENNReal.ofReal (μ[f 0]) := by
    simpa [bad, ε] using
      ville_inequality (μ := μ) (𝒢 := 𝒢) (f := f) hsuper hnonneg (ε := ε)
  have hstart_enn : ENNReal.ofReal (μ[f 0]) ≤ 1 := by
    simpa using (ENNReal.ofReal_le_ofReal hstart)
  have hscaled : (α⁻¹ : NNReal) * μ bad ≤ 1 := hville.trans hstart_enn
  have hmul : (α : ℝ≥0∞) * ((α⁻¹ : NNReal) * μ bad) ≤ (α : ℝ≥0∞) * 1 := by gcongr
  have hα_ne_zero : (α : ℝ≥0∞) ≠ 0 := by exact_mod_cast hα.ne'
  have hcoe_inv : ((α⁻¹ : NNReal) : ℝ≥0∞) = (α : ℝ≥0∞)⁻¹ := ENNReal.coe_inv hα.ne'
  have hcancel :
      (α : ℝ≥0∞) * ((α⁻¹ : NNReal) * μ bad) = μ bad := by
    rw [hcoe_inv]
    exact ENNReal.mul_inv_cancel_left (a := (α : ℝ≥0∞)) (b := μ bad)
      hα_ne_zero ENNReal.coe_ne_top
  change μ bad ≤ (α : ℝ≥0∞)
  rw [← hcancel]
  simpa using hmul

end

end

end MeasureTheory
