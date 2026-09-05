/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Defs.Cadlag
public import Mathlib.Probability.Process.Adapted

/-! # Strong measurability of the path map of a right-continuous process

A process `X : ι → Ω → E` can be seen as a path-valued random variable `Ω → (ι → E)`, where
`ι → E` carries the product topology. We show that if each `X i` is strongly measurable and
every path `X · ω` is right-continuous, then that path map is strongly measurable.

## Main results

* `stronglyMeasurable_path_of_isRightContinuous`: the path map of a right-continuous process
  with strongly measurable marginals is strongly measurable.
* `StronglyAdapted.stronglyMeasurable_path`: the same statement for a strongly
  adapted process with right-continuous paths.

-/

open Filter Set TopologicalSpace
open scoped Topology

namespace MeasureTheory

variable {ι Ω E : Type*} [LinearOrder ι] {mΩ : MeasurableSpace Ω} {X : ι → Ω → E}

section PathApprox

variable [MeasurableSpace E] [PseudoEMetricSpace E] [OpensMeasurableSpace E] [AddCommMonoid E]
  {e : ℕ → E} {s : Finset ι} {n : ℕ}

open scoped Classical in
/-- The simple function sending `ω` to the step function taking at `i` the value
`SimpleFunc.nearestPt e n (X t ω)`, where `t` is the smallest element of `s` with `i ≤ t`
(and the value `0` if `s` has no element `≥ i`). -/
noncomputable def pathApprox (X : ι → Ω → E) (hX : ∀ t, Measurable (X t)) (e : ℕ → E)
    (s : Finset ι) (n : ℕ) :
    SimpleFunc Ω (ι → E) :=
  ∑ t ∈ s, ((SimpleFunc.nearestPt e n).comp (X t) (hX t)).map
    fun w i ↦ if IsLeast {u ∈ s | i ≤ u} t then w else 0

open scoped Classical in
lemma pathApprox_apply (hX : ∀ t, Measurable (X t)) (ω : Ω) (i : ι) :
    pathApprox X hX e s n ω i =
      ∑ t ∈ s, if IsLeast {u ∈ s | i ≤ u} t then SimpleFunc.nearestPt e n (X t ω) else 0 := by
  simp [pathApprox, SimpleFunc.coe_finsetSum]

/-- Evaluation of `pathApprox` at a time `i` for which `t₀` is the smallest element of `s`
that is `≥ i`. -/
lemma pathApprox_apply_of_isLeast (hX : ∀ t, Measurable (X t)) {ω : Ω} {i t₀ : ι}
    (h : IsLeast {u ∈ s | i ≤ u} t₀) :
    pathApprox X hX e s n ω i = SimpleFunc.nearestPt e n (X t₀ ω) := by
  rw [pathApprox_apply hX, Finset.sum_eq_single t₀] <;> grind [IsLeast, lowerBounds]

end PathApprox

public section RightContinuous

variable [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]

/-- The set of values taken by a right-continuous process with strongly measurable marginals
is separable. -/
lemma isSeparable_iUnion_range_of_stronglyMeasurable_of_isRightContinuous [TopologicalSpace E]
    (hX : ∀ i, StronglyMeasurable (X i)) (hX_cont : ∀ ω, IsRightContinuous (X · ω)) :
    IsSeparable (⋃ t, range (X t)) := by
  obtain ⟨d, hd_count, hd_dense⟩ := exists_countable_dense ι
  let D : Set ι := d ∪ {x : ι | 𝓝[>] x = ⊥}
  have hD_count : D.Countable := hd_count.union countable_setOfPred_isolated_right
  have hD_ne i (hi : i ∉ D) : (𝓝[>] i).NeBot := ⟨fun h ↦ hi (mem_union_right _ h)⟩
  obtain ⟨c, hc_count, hc⟩ : IsSeparable (⋃ t : D, range (X t)) := by
    have : Countable D := hD_count.to_subtype
    exact IsSeparable.iUnion fun t ↦ (hX t).isSeparable_range
  refine ⟨c, hc_count, fun x hx ↦ ?_⟩
  simp only [mem_iUnion, mem_range] at hx
  obtain ⟨i, ω, rfl⟩ := hx
  by_cases hi : i ∈ D
  · exact hc (mem_iUnion.2 ⟨⟨i, hi⟩, ⟨ω, rfl⟩⟩)
  have := hD_ne i hi
  have : (𝓝[d ∩ Ioi i] i).NeBot := hd_dense.nhdsWithin_inter_neBot isOpen_Ioi
  have h1 : Tendsto (X · ω) (𝓝[d ∩ Ioi i] i) (𝓝 (X i ω)) :=
    (hX_cont ω i).mono_left (nhdsWithin_mono i inter_subset_right)
  refine isClosed_closure.mem_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht using
    hc (mem_iUnion.2 ⟨⟨t, mem_union_left _ ht.1⟩, ⟨ω, rfl⟩⟩)

variable [PseudoMetricSpace E] [AddCommMonoid E]

/-- A process whose paths are right-continuous and whose marginals `X i` are strongly measurable
is strongly measurable as a map `Ω → (ι → E)` into the path space with the product topology. -/
lemma stronglyMeasurable_path_of_isRightContinuous
    (hX : ∀ i, StronglyMeasurable (X i)) (hX_cont : ∀ ω, IsRightContinuous (X · ω)) :
    StronglyMeasurable (fun ω ↦ (X · ω)) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  borelize E
  have hX_meas i : Measurable (X i) := (hX i).measurable
  -- The countable set `D` of discretization times: a countable dense set together with the
  -- points that are isolated on the right, at which right-continuity says nothing.
  obtain ⟨d, hd_count, hd_dense⟩ := exists_countable_dense ι
  let D : Set ι := d ∪ {x : ι | 𝓝[>] x = ⊥}
  have hD_count : D.Countable := hd_count.union countable_setOfPred_isolated_right
  have hD_ne i (hi : i ∉ D) : (𝓝[>] i).NeBot := ⟨fun h ↦ hi (mem_union_right _ h)⟩
  let q : ℕ → ι := enumerateCountable hD_count (Classical.arbitrary ι)
  have hDq : D ⊆ range q := subset_range_enumerate hD_count _
  let times : ℕ → Finset ι := fun n ↦ (Finset.range n).image q
  have hq_mem k n (hkn : k < n) : q k ∈ times n := by
    simpa [times] using ⟨k, hkn, rfl⟩
  -- A single sequence `e` of values, dense in the set of all values taken by the process.
  obtain ⟨c, hc_count, hc⟩ : IsSeparable (⋃ t, range (X t)) :=
    isSeparable_iUnion_range_of_stronglyMeasurable_of_isRightContinuous hX hX_cont
  let e : ℕ → E := enumerateCountable hc_count 0
  have hce : c ⊆ range e := subset_range_enumerate hc_count _
  -- Every value of the process lies in the closure of `range e`: either the time is one of the
  -- discretization times, or right-continuity exhibits the value as a limit of such values.
  have hXmem i ω : X i ω ∈ closure (range e) :=
    closure_mono hce (hc (mem_iUnion.2 ⟨i, ⟨ω, rfl⟩⟩))
  -- The approximating simple functions.
  refine ⟨fun n ↦ pathApprox X hX_meas e (times n) n,
    fun ω ↦ tendsto_pi_nhds.2 fun i ↦ EMetric.tendsto_atTop.2 fun ε hε ↦ ?_⟩
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  -- A point `e k` close to `X i ω`.
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := EMetric.mem_closure_iff.1 (hXmem i ω) (ε / 3) hε3
  -- Eventually, the smallest discretization time `≥ i` carries a value close to `X i ω`.
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, ∃ t₀, (IsLeast {u ∈ times n | i ≤ u} t₀) ∧
      edist (X t₀ ω) (X i ω) < ε / 3 := by
    obtain hi | _ := (𝓝[>] i).eq_or_neBot
    · -- `i` is itself a discretization time, and is then its own rounding.
      obtain ⟨ki, hki⟩ := hDq (mem_union_right _ hi)
      exact ⟨ki + 1, fun n hn ↦ ⟨i, ⟨⟨hki ▸ hq_mem ki n hn, le_rfl⟩, fun u hu ↦ hu.2⟩,
        by simpa using hε3⟩⟩
    · -- `i` is not isolated on the right, so right-continuity applies.
      obtain ⟨u', hu'⟩ : ∃ u, i < u :=
        nonempty_of_mem (self_mem_nhdsWithin (a := i) (s := Ioi i))
      obtain ⟨u, hiu, hu, hud⟩ :
          ∃ u > i, Ioc i u ⊆ (X · ω) ⁻¹' Metric.eball (X i ω) (ε / 3) ∧ u ∈ d := by
        obtain ⟨v, hiv, hv⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hu').mp
          ((hX_cont ω i) (Metric.eball_mem_nhds (X i ω) hε3))
        obtain ⟨u, hu⟩ := hd_dense.inter_open_nonempty (Ioo i v) isOpen_Ioo <|
          nonempty_of_mem (Ioo_mem_nhdsGT hiv)
        exact ⟨u, by grind⟩
      obtain ⟨kv, hkv⟩ : ∃ n, q n = u := hDq (mem_union_left _ hud)
      have hiv : i ≤ q kv := by grind
      have hvu : q kv ≤ u := by grind
      refine ⟨kv + 1, fun n hn ↦ ?_⟩
      let T : Finset ι := {t ∈ times n | i ≤ t}
      have hTne : T.Nonempty := ⟨q kv, Finset.mem_filter.2 ⟨hq_mem kv n hn, hiv⟩⟩
      have hit₀ : i ≤ T.min' hTne := (Finset.mem_filter.1 (T.min'_mem hTne)).2
      have ht₀u : T.min' hTne ≤ u :=
        (T.min'_le _ (Finset.mem_filter.2 ⟨hq_mem kv n hn, hiv⟩)).trans hvu
      refine ⟨T.min' hTne, by simpa [T] using T.isLeast_min' hTne, ?_⟩
      rcases hit₀.lt_or_eq with h | h
      · exact Metric.mem_eball.1 (hu ⟨h, ht₀u⟩)
      · simpa [h] using hε3
  refine ⟨max k N₀, fun n hn ↦ ?_⟩
  obtain ⟨t₀, ht₀, hclose⟩ := hN₀ n ((le_max_right _ _).trans hn)
  rw [pathApprox_apply_of_isLeast hX_meas ht₀]
  calc edist (SimpleFunc.nearestPt e n (X t₀ ω)) (X i ω)
  _ ≤ edist (SimpleFunc.nearestPt e n (X t₀ ω)) (X t₀ ω) + edist (X t₀ ω) (X i ω) :=
      edist_triangle _ _ _
  _ ≤ edist (e k) (X t₀ ω) + edist (X t₀ ω) (X i ω) := by
      gcongr
      exact SimpleFunc.edist_nearestPt_le e _ (by grind)
  _ ≤ edist (e k) (X i ω) + edist (X i ω) (X t₀ ω) + edist (X t₀ ω) (X i ω) := by
      grw [edist_triangle]
  _ < ε / 3 + ε / 3 + ε / 3 := by rw [edist_comm (X i ω), edist_comm (e k)]; gcongr
  _ = ε := by norm_num

/-- A strongly adapted process with right-continuous paths is strongly measurable as a path-valued
random variable `Ω → (ι → E)`. -/
lemma StronglyAdapted.stronglyMeasurable_path {𝓕 : Filtration ι mΩ}
    (hX : StronglyAdapted 𝓕 X) (hX_cont : ∀ ω, IsRightContinuous (X · ω)) :
    StronglyMeasurable (fun ω ↦ (X · ω)) :=
  stronglyMeasurable_path_of_isRightContinuous (fun i ↦ (hX i).mono (𝓕.le i)) hX_cont

end RightContinuous

end MeasureTheory
