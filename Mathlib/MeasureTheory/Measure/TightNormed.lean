/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Order.CompletePartialOrder

/-!
# Tight sets of measures in normed spaces

Criteria for tightness of sets of measures in normed and inner product spaces.

## Main statements

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: in a proper normed group, a set of measures `S`
  is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity.
* `isTightMeasureSet_iff_inner_tendsto`: in a finite-dimensional inner product space,
  a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < |⟪y, x⟫|}`
  tends to `0` at infinity for all `y`.
* `isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt`: in a proper normed group,
  the range of a sequence of measures `μ : ℕ → Measure E` is tight if and only if the function
  `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to `0` at infinity.
* `isTightMeasureSet_range_iff_tendsto_limsup_inner`: in a finite-dimensional inner product space,
  the range of a sequence of measures `μ : ℕ → Measure E` is tight if and only if the function
  `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop` tends to `0` at infinity for all `y`.

-/

open Filter

open scoped Topology ENNReal InnerProductSpace

/-- Let `u : ι → α → β` be a sequence of antitone functions `α → β` indexed by `ι`. Suppose that for
all `i : ι`, `u i` tends to `c` at infinity, and that furthermore the limsup of `i ↦ u i r` along
the cofinite filter tends to the same `c` as `r` tends to infinity.
Then the supremum function `r ↦ ⨆ i, u i r` also tends to `c` at infinity. -/
lemma tendsto_iSup_of_tendsto_limsup {α : Type*} [ConditionallyCompleteLattice α] {β : Type*}
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {ι : Type*}
    {u : ι → α → β} {c : β}
    (h_all : ∀ i, Tendsto (u i) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α ↦ limsup (fun i ↦ u i r) cofinite) atTop (𝓝 c))
    (h_anti : ∀ i, Antitone (u i)) :
    Tendsto (fun r : α ↦ ⨆ i, u i r) atTop (𝓝 c) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨n0⟩⟩
  · simpa using h_limsup
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [] with r
    have : c ≤ u n0 r := Antitone.le_of_tendsto (h_anti n0) (h_all n0) r
    exact hb.trans_le (this.trans (le_iSup_iff.mpr fun b a ↦ a n0))
  let b' := if h : (Set.Ioo c b).Nonempty then h.some else c
  have hb'b : b' < b := by
    simp only [b']
    split_ifs with h
    exacts [h.some_mem.2, hb]
  have : ∀ᶠ r in atTop, limsup (fun n ↦ u n r) cofinite ≤ b' := by
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 h_limsup).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 h_limsup).2 b hb] with r hr
      contrapose! h
      exact ⟨limsup (fun n ↦ u n r) cofinite, h, hr⟩
  obtain ⟨r, hr⟩ : ∃ r, ∀ s ≥ r, limsup (fun n ↦ u n s) cofinite ≤ b' := by simpa using this
  obtain ⟨b'', hb''b, hb''⟩ : ∃ b'' ∈ Set.Ico b' b, ∀ᶠ n in cofinite, u n r ≤ b'' := by
    rcases Set.eq_empty_or_nonempty (Set.Ioo b' b) with h | ⟨b'', hb'b'', hb''b⟩
    · refine ⟨b', ⟨le_rfl, hb'b⟩, ?_⟩
      have := hr r le_rfl
      rw [limsup_le_iff] at this
      filter_upwards [this b hb'b] with n hn
      contrapose! h
      exact ⟨u n r, h, hn⟩
    · refine ⟨b'', ⟨hb'b''.le, hb''b⟩ , ?_⟩
      have := hr r le_rfl
      rw [limsup_le_iff] at this
      filter_upwards [this b'' hb'b''] with n hn using hn.le
  have A (n) : ∃ r, ∀ s ≥ r, u n s ≤ b'' := by
    suffices ∀ᶠ r in atTop, u n r ≤ b' by
      simp only [eventually_atTop, ge_iff_le] at this
      rcases this with ⟨r, hr⟩
      exact ⟨r, fun s hs ↦ (hr s hs).trans hb''b.1⟩
    simp only [b']
    split_ifs with h
    · filter_upwards [(tendsto_order.1 (h_all n)).2 _ h.some_mem.1] with r hr
      exact hr.le
    · filter_upwards [(tendsto_order.1 (h_all n)).2 b hb] with r hr
      contrapose! h
      exact ⟨u n r, h, hr⟩
  choose rs hrs using A
  simp only [eventually_atTop, ge_iff_le]
  refine ⟨r ⊔ ⨆ n : {n | b'' < u n r}, rs n, fun v hv ↦ ?_⟩
  apply lt_of_le_of_lt _ hb''b.2
  simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
  intro n
  by_cases hn : b'' < u n r
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : {n | b'' < u n r}) := rfl
    _ ≤ ⨆ n : {n | b'' < u n r}, rs n := by
      refine le_ciSup (f := fun (x : {n | b'' < u n r}) ↦ rs x) ?_
        (⟨n, by simp [hn]⟩ : {n | b'' < u n r})
      have : Finite {n | b'' < u n r} := by simpa using hb''
      apply Finite.bddAbove_range _
    _ ≤ r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_right
    _ ≤ v := hv
  · simp at hn
    refine (h_anti n ?_).trans hn
    calc r
    _ ≤ r ⊔ ⨆ n : {n | b'' < u n r}, rs n := le_sup_left
    _ ≤ v := hv

/-- Let `u : ℕ → α → β` be a sequence of antitone functions `α → β` indexed by `ℕ`. Suppose that for
all `n : ℕ`, `u n` tends to `c` at infinity, and that furthermore the limsup of `n ↦ u n r`
tends to the same `c` as `r` tends to infinity.
Then the supremum function `r ↦ ⨆ n, u n r` also tends to `c` at infinity. -/
nonrec
lemma Nat.tendsto_iSup_of_tendsto_limsup {α : Type*} [ConditionallyCompleteLattice α] {β : Type*}
    [CompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {u : ℕ → α → β} {c : β}
    (h_all : ∀ n, Tendsto (u n) atTop (𝓝 c))
    (h_limsup : Tendsto (fun r : α ↦ limsup (fun n ↦ u n r) atTop) atTop (𝓝 c))
    (h_anti : ∀ n, Antitone (u n)) :
    Tendsto (fun r : α ↦ ⨆ n, u n r) atTop (𝓝 c) := by
  refine tendsto_iSup_of_tendsto_limsup  h_all ?_ h_anti
  convert h_limsup
  exact cofinite_eq_atTop

namespace MeasureTheory

variable {E : Type*} {mE : MeasurableSpace E} {S : Set (Measure E)}

section PseudoMetricSpace

variable [PseudoMetricSpace E]

lemma tendsto_measure_compl_closedBall_of_isTightMeasureSet (hS : IsTightMeasureSet S) (x : E) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) := by
  suffices Tendsto ((⨆ μ ∈ S, μ) ∘ (fun r ↦ (Metric.closedBall x r)ᶜ)) atTop (𝓝 0) by
    convert this with r
    simp
  refine hS.comp <| .mono_right ?_ <| monotone_smallSets Metric.cobounded_le_cocompact
  exact (Metric.hasAntitoneBasis_cobounded_compl_closedBall _).tendsto_smallSets

lemma isTightMeasureSet_of_tendsto_measure_compl_closedBall [ProperSpace E] {x : E}
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  exact ⟨Metric.closedBall x r, isCompact_closedBall x r, by simpa using h r le_rfl⟩

/-- In a proper pseudo-metric space, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ` tends to `0` at infinity. -/
lemma isTightMeasureSet_iff_tendsto_measure_compl_closedBall [ProperSpace E] (x : E) :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ (Metric.closedBall x r)ᶜ) atTop (𝓝 0) :=
  ⟨fun hS ↦ tendsto_measure_compl_closedBall_of_isTightMeasureSet hS x,
    isTightMeasureSet_of_tendsto_measure_compl_closedBall⟩

end PseudoMetricSpace

section NormedAddCommGroup

variable [NormedAddCommGroup E]

lemma tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_compl_closedBall_of_isTightMeasureSet hS 0
  convert h using 6 with r
  ext
  simp

lemma isTightMeasureSet_of_tendsto_measure_norm_gt [ProperSpace E]
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tendsto_measure_compl_closedBall (x := 0) ?_
  convert h using 6 with r
  ext
  simp

/-- In a proper normed group, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity. -/
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt [ProperSpace E] :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

section Sequence

variable [BorelSpace E] [ProperSpace E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]

/-- For a sequence of measures indexed by `ℕ`, if the function
`r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to 0 at infinity, then the set of measures
in the sequence is tight.
Compared to `isTightMeasureSet_of_tendsto_measure_norm_gt`, this lemma replaces a supremum over
all measures by a limsup. -/
lemma isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt
    (h : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  simp_rw [iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) h fun n u v huv ↦ ?_
  · have h_tight : IsTightMeasureSet {μ n} := isTightMeasureSet_singleton
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
    simpa using h_tight
  · refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact huv.trans_lt hx

/-- For a sequence of measures indexed by `ℕ`, the set of measures in the sequence is tight if and
only if the function `r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop` tends to 0 at infinity.
Compared to `isTightMeasureSet_iff_tendsto_measure_norm_gt`, this lemma replaces a supremum over
all measures by a limsup. -/
lemma isTightMeasureSet_range_iff_tendsto_limsup_measure_norm_gt :
    IsTightMeasureSet (Set.range μ)
      ↔ Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, isTightMeasureSet_range_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ ↦ zero_le') ?_
  intro r
  simp_rw [iSup_range]
  exact limsup_le_iSup

end Sequence

section InnerProductSpace

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

lemma isTightMeasureSet_of_forall_basis_tendsto (b : OrthonormalBasis ι 𝕜 E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪b i, x⟫_𝕜‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simpa [← Module.finrank_eq_card_basis b.toBasis, Module.finrank_pos_iff]
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have h_le : (fun r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖})
      ≤ fun r ↦ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
    intro r
    calc ⨆ μ ∈ S, μ {x | r < ‖x‖}
    _ ≤ ⨆ μ ∈ S, μ (⋃ i, {x : E | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖}) := by
      gcongr with μ hμS
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
      have hx' : r < √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫_𝕜‖ :=
        hx.trans_le (b.norm_le_card_mul_iSup_norm_inner x)
      rw [← div_lt_iff₀' (by positivity)] at hx'
      by_contra! h_le
      exact lt_irrefl (r / √(Fintype.card ι)) (hx'.trans_le (ciSup_le h_le))
    _ ≤ ⨆ μ ∈ S, ∑ i, μ {x : E | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
      gcongr with μ hμS
      exact measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖} := by
      refine iSup_le fun μ ↦ (iSup_le fun hμS ↦ ?_)
      gcongr with i
      exact le_biSup (fun μ ↦ μ {x | r / √(Fintype.card ι) < ‖⟪b i, x⟫_𝕜‖}) hμS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') h_le
  rw [← Finset.sum_const_zero]
  refine tendsto_finset_sum Finset.univ fun i _ ↦ (h i).comp ?_
  exact tendsto_id.atTop_div_const (by positivity)

variable (𝕜)

lemma isTightMeasureSet_of_inner_tendsto
    (h : ∀ y, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_forall_basis_tendsto (stdOrthonormalBasis 𝕜 E)
    fun i ↦ h (stdOrthonormalBasis 𝕜 E i)

/-- In a finite-dimensional inner product space,
a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < |⟪y, x⟫|}`
tends to `0` at infinity for all `y`. -/
lemma isTightMeasureSet_iff_inner_tendsto :
    IsTightMeasureSet S
      ↔ ∀ y, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖⟪y, x⟫_𝕜‖}) atTop (𝓝 0) := by
  refine ⟨fun h y ↦ ?_, isTightMeasureSet_of_inner_tendsto 𝕜⟩
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left, abs_zero]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r ↦ ⨆ μ ∈ S, μ {x | r * ‖y‖⁻¹ < ‖x‖}) atTop (𝓝 0) :=
    h.comp <| (tendsto_mul_const_atTop_of_pos (by positivity)).mpr tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h' (fun _ ↦ zero_le') ?_
  intro r
  have h_le (μ : Measure E) : μ {x | r < ‖⟪y, x⟫_𝕜‖} ≤ μ {x | r * ‖y‖⁻¹ < ‖x‖} := by
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [mul_inv_lt_iff₀]
    · rw [mul_comm]
      exact hx.trans_le (norm_inner_le_norm y x)
    · positivity
  refine iSup₂_le_iff.mpr fun μ hμS ↦ ?_
  exact le_iSup_of_le (i := μ) <| by simp [hμS, h_le]

variable [BorelSpace E] {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]

lemma isTightMeasureSet_range_of_tendsto_limsup_inner
    (h : ∀ y, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_of_inner_tendsto 𝕜 fun z ↦ ?_
  simp_rw [iSup_range]
  refine Nat.tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) (h z) fun n u v huv ↦ ?_
  · have h_tight : IsTightMeasureSet {(μ n).map (fun x ↦ ⟪z, x⟫_𝕜)} := isTightMeasureSet_singleton
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
    have h_map r : (μ n).map (fun x ↦ ⟪z, x⟫_𝕜) {x | r < ‖x‖} = μ n {x | r < ‖⟪z, x⟫_𝕜‖} := by
      rw [Measure.map_apply (by fun_prop)]
      · simp
      · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    simpa [h_map] using h_tight
  · exact measure_mono fun x hx ↦ huv.trans_lt hx

/-- In a finite-dimensional inner product space, the range of a sequence of measures
`μ : ℕ → Measure E` is tight if and only if the function
`r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop` tends to `0` at infinity for all `y`. -/
lemma isTightMeasureSet_range_iff_tendsto_limsup_inner :
    IsTightMeasureSet (Set.range μ)
      ↔ ∀ y, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h z ↦ ?_, isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜⟩
  rw [isTightMeasureSet_iff_inner_tendsto 𝕜] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h z)
    (fun _ ↦ zero_le') fun r ↦ ?_
  simp_rw [iSup_range]
  exact limsup_le_iSup

lemma isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one
    (h : ∀ y, ‖y‖ = 1
      → Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner 𝕜 fun y ↦ ?_
  by_cases hy : y = 0
  · simp only [hy, inner_zero_left, abs_zero]
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 0] with r hr
    simp [not_lt.mpr hr]
  have h' : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | ‖y‖⁻¹ * r < ‖⟪(‖y‖⁻¹ : 𝕜) • y, x⟫_𝕜‖})
      atTop) atTop (𝓝 0) := by
    specialize h ((‖y‖⁻¹ : 𝕜) • y) ?_
    · simp only [norm_smul, norm_inv, norm_algebraMap', Real.norm_eq_abs, abs_norm]
      rw [inv_mul_cancel₀ (by positivity)]
    exact h.comp <| (tendsto_const_mul_atTop_of_pos (by positivity)).mpr tendsto_id
  convert h' using 7 with r n x
  rw [inner_smul_left]
  simp only [map_inv₀, RCLike.conj_ofReal, norm_mul, norm_inv, norm_algebraMap', norm_norm]
  rw [mul_lt_mul_left]
  positivity

end InnerProductSpace

end NormedAddCommGroup

end MeasureTheory
