/-
Copyright (c) 2026 Matthew W. Horn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew W. Horn
-/
module

public import Mathlib.Probability.Distributions.Geometric

/-! # Censored geometric distributions

For `p : unitInterval` and `m : ℕ`, `geometricCensoredMeasure p m` is the distribution of
`min k m` for `k` geometric with success probability `p`: the pushforward of
`geometricMeasure p` under `fun k ↦ min k m`. The mass of `{m, m + 1, ...}` collects at `m`;
nothing is renormalized. This is censoring, not truncation (which conditions on `k ≤ m` and
renormalizes).

## Main definitions

* `geometricCensoredMeasure p m`: the geometric distribution censored at `m`.

## Main results

* `geometricCensoredMeasure_singleton_of_lt`, `geometricCensoredMeasure_singleton_self`,
  `geometricCensoredMeasure_singleton_of_gt`: the censored mass function: `(1 - p) ^ k * p`
  below `m`, the whole tail `(1 - p) ^ m` at `m`, and `0` above `m`.

## Tags

geometric distribution, censoring
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {p : unitInterval} {m k : ℕ}

/-- The geometric distribution with success probability `p`, censored at `m`: the distribution
of `min k m` for `k` geometric. The mass of `{m, m + 1, ...}` collects at `m`; nothing is
renormalized. -/
noncomputable def geometricCensoredMeasure (p : unitInterval) (m : ℕ) : Measure ℕ :=
  (geometricMeasure p).map fun k ↦ min k m

instance isProbabilityMeasure_geometricCensoredMeasure :
    IsProbabilityMeasure (geometricCensoredMeasure p m) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

/-- The censored measure of a set is the geometric measure of its preimage under
`fun k ↦ min k m`. -/
lemma geometricCensoredMeasure_apply (s : Set ℕ) :
    geometricCensoredMeasure p m s = geometricMeasure p ((fun k ↦ min k m) ⁻¹' s) :=
  Measure.map_apply Measurable.of_discrete .of_discrete

/-- Below the censoring point, the censored distribution keeps the geometric mass
`(1 - p) ^ k * p`. -/
lemma geometricCensoredMeasure_singleton_of_lt (hp : p ≠ 0) (hk : k < m) :
    geometricCensoredMeasure p m {k} = ENNReal.ofReal ((1 - p) ^ k * p) := by
  have hpre : (fun n ↦ min n m) ⁻¹' {k} = {k} := by
    ext n
    simp only [mem_preimage, mem_singleton_iff]
    omega
  rw [geometricCensoredMeasure_apply, hpre, geometricMeasure_singleton hp]

/-- At the censoring point, the censored distribution collects the whole geometric tail
`(1 - p) ^ m`. -/
lemma geometricCensoredMeasure_singleton_self (hp : p ≠ 0) :
    geometricCensoredMeasure p m {m} = ENNReal.ofReal ((1 - p) ^ m) := by
  have hpre : (fun n ↦ min n m) ⁻¹' {m} = Ici m := by
    ext n
    simp only [mem_preimage, mem_singleton_iff, mem_Ici]
    omega
  rw [geometricCensoredMeasure_apply, hpre, geometricMeasure_Ici hp]

/-- Above the censoring point, the censored distribution has no mass. -/
lemma geometricCensoredMeasure_singleton_of_gt (hk : m < k) :
    geometricCensoredMeasure p m {k} = 0 := by
  have hpre : (fun n ↦ min n m) ⁻¹' {k} = ∅ := by
    ext n
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    omega
  rw [geometricCensoredMeasure_apply, hpre, measure_empty]

end ProbabilityTheory
