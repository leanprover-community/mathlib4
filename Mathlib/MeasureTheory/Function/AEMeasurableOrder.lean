/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability criterion for ennreal-valued functions

Consider a function `f : α → ℝ≥0∞`. If the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. This is proved in
`ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`, and deduced from an analogous statement
for any target space which is a complete linear dense order, called
`MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets`.

Note that it should be enough to assume that the space is a conditionally complete linear order,
but the proof would be more painful. Since our only use for now is for `ℝ≥0∞`, we keep it as simple
as possible.
-/

public section


open MeasureTheory Set TopologicalSpace

open ENNReal NNReal

/-- If a function `f : α → β` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p < q`, then `f` is almost-everywhere
measurable. It is even enough to have this for `p` and `q` in a countable dense set. -/
theorem MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*}
    {m : MeasurableSpace α} (μ : Measure α) {β : Type*} [CompleteLinearOrder β] [DenselyOrdered β]
    [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β] [MeasurableSpace β]
    [BorelSpace β] (s : Set β) (s_count : s.Countable) (s_dense : Dense s) (f : α → β)
    (h : ∀ p ∈ s, ∀ q ∈ s, p < q → ∃ u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AEMeasurable f μ := by
  classical
  haveI : Encodable s := s_count.toEncodable
  have h' : ∀ p q, ∃ u v, MeasurableSet u ∧ MeasurableSet v ∧
      { x | f x < p } ⊆ u ∧ { x | q < f x } ⊆ v ∧ (p ∈ s → q ∈ s → p < q → μ (u ∩ v) = 0) := by
    intro p q
    by_cases H : p ∈ s ∧ q ∈ s ∧ p < q
    · rcases h p H.1 q H.2.1 H.2.2 with ⟨u, v, hu, hv, h'u, h'v, hμ⟩
      exact ⟨u, v, hu, hv, h'u, h'v, fun _ _ _ => hμ⟩
    · refine
        ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, subset_univ _, subset_univ _,
          fun ps qs pq => ?_⟩
      exact (H ⟨ps, qs, pq⟩).elim
  choose! u v huv using h'
  let u' : β → Set α := fun p => ⋂ q ∈ s ∩ Ioi p, u p q
  have u'_meas : ∀ i, MeasurableSet (u' i) := by
    intro i
    exact MeasurableSet.biInter (s_count.mono inter_subset_left) fun b _ => (huv i b).1
  let f' : α → β := fun x => ⨅ i : s, piecewise (u' i) (fun _ => (i : β)) (fun _ => (⊤ : β)) x
  have f'_meas : Measurable f' := by fun_prop (disch := simp_all)
  let t := ⋃ (p : s) (q : ↥(s ∩ Ioi p)), u' p ∩ v p q
  have μt : μ t ≤ 0 :=
    calc
      μ t ≤ ∑' (p : s) (q : ↥(s ∩ Ioi p)), μ (u' p ∩ v p q) := by
        refine (measure_iUnion_le _).trans ?_
        refine ENNReal.tsum_le_tsum fun p => ?_
        haveI := (s_count.mono (s.inter_subset_left (t := Ioi ↑p))).to_subtype
        apply measure_iUnion_le
      _ ≤ ∑' (p : s) (q : ↥(s ∩ Ioi p)), μ (u p q ∩ v p q) := by
        gcongr with p q
        exact biInter_subset_of_mem q.2
      _ = ∑' (p : s) (_ : ↥(s ∩ Ioi p)), (0 : ℝ≥0∞) := by grind
      _ = 0 := by simp only [tsum_zero]
  have ff' : ∀ᵐ x ∂μ, f x = f' x := by
    have : ∀ᵐ x ∂μ, x ∉ t := by
      exact measure_eq_zero_iff_ae_notMem.1 (le_antisymm μt bot_le)
    filter_upwards [this] with x hx
    apply (iInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _).symm
    · intro i
      by_cases H : x ∈ u' i
      swap
      · simp only [H, le_top, not_false_iff, piecewise_eq_of_notMem]
      simp only [H, piecewise_eq_of_mem]
      contrapose! hx
      obtain ⟨r, rs, xr, rq⟩ := s_dense.exists_between hx
      exact mem_iUnion₂.2 ⟨i, ⟨⟨r, ⟨rs, xr⟩⟩, H, (huv i r).2.2.2.1 rq⟩⟩
    · intro q hq
      obtain ⟨r, rs, xr, rq⟩ := s_dense.exists_between hq
      exact ⟨⟨r, rs⟩, by
        simp only [show x ∈ u' r from mem_biInter fun i _ => (huv r i).2.2.1 xr, rq,
          piecewise_eq_of_mem]⟩
  exact ⟨f', f'_meas, ff'⟩

/-- If a function `f : α → ℝ≥0∞` is such that the level sets `{f < p}` and `{q < f}` have measurable
supersets which are disjoint up to measure zero when `p` and `q` are finite numbers satisfying
`p < q`, then `f` is almost-everywhere measurable. -/
theorem ENNReal.aemeasurable_of_exist_almost_disjoint_supersets {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) (f : α → ℝ≥0∞)
    (h : ∀ (p : ℝ≥0) (q : ℝ≥0), p < q →
      ∃ u v, MeasurableSet u ∧ MeasurableSet v ∧
        { x | f x < p } ⊆ u ∧ { x | (q : ℝ≥0∞) < f x } ⊆ v ∧ μ (u ∩ v) = 0) :
    AEMeasurable f μ := by
  obtain ⟨s, s_count, s_dense, _, s_top⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : ∀ x ∈ s, x ≠ ∞ := fun x xs hx => s_top (hx ▸ xs)
  apply MeasureTheory.aemeasurable_of_exist_almost_disjoint_supersets μ s s_count s_dense _
  rintro p hp q hq hpq
  lift p to ℝ≥0 using I p hp
  lift q to ℝ≥0 using I q hq
  exact h p q (ENNReal.coe_lt_coe.1 hpq)
