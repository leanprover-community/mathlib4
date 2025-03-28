/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tight sets of measures in normed spaces

Criteria for tightness of sets of measures in normed and inner product spaces.

## Main statements

* `isTightMeasureSet_iff_tendsto_measure_norm_gt`: in a finite dimensional real normed space,
  a set of measures `S` is tight if and only if the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}`
  tends to `0` at infinity.

-/

open Filter

open scoped Topology ENNReal RealInnerProductSpace

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {mE : MeasurableSpace E} {S : Set (Measure E)}

lemma isTightMeasureSet_singleton {α : Type*} {mα : MeasurableSpace α}
  [PseudoEMetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [BorelSpace α]
  {μ : Measure α} [IsFiniteMeasure μ] :
    IsTightMeasureSet {μ} :=
  isTightMeasureSet_singleton_of_innerRegularWRT
    (innerRegular_isCompact_isClosed_measurableSet_of_finite _)

lemma tendsto_iSup_of_tendsto_limsup {u : ℕ → ℝ → ℝ≥0∞}
    (h_all : ∀ n, Tendsto (u n) atTop (𝓝 0))
    (h_tendsto : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ u n r) atTop) atTop (𝓝 0))
    (h_anti : ∀ n, Antitone (u n)) :
    Tendsto (fun r : ℝ ↦ ⨆ n, u n r) atTop (𝓝 0) := by
  simp_rw [ENNReal.tendsto_atTop_zero] at h_tendsto h_all ⊢
  intro ε hε
  by_cases hε_top : ε = ∞
  · refine ⟨0, fun _ _ ↦ by simp [hε_top]⟩
  simp only [gt_iff_lt, ge_iff_le] at h_tendsto h_all hε
  obtain ⟨r, h⟩ := h_tendsto (ε / 2) (ENNReal.half_pos hε.ne')
  have h' x (hx : r ≤ x) y (hy : ε / 2 < y) : ∀ᶠ n in atTop, u n x < y := by
    specialize h x hx
    rw [limsup_le_iff] at h
    exact h y hy
  replace h' : ∀ x, r ≤ x → ∀ᶠ n in atTop, u n x < ε :=
    fun x hx ↦ h' x hx ε (ENNReal.half_lt_self hε.ne' hε_top)
  simp only [eventually_atTop, ge_iff_le] at h'
  obtain ⟨N, h⟩ := h' r le_rfl
  replace h_all : ∀ ε > 0, ∀ n, ∃ N, ∀ n_1 ≥ N, u n n_1 ≤ ε := fun ε hε n ↦ h_all n ε hε
  choose rs hrs using h_all ε hε
  refine ⟨r ⊔ ⨆ n : Finset.range N, rs n, fun v hv ↦ ?_⟩
  simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
  intro n
  by_cases hn : n < N
  · refine hrs n v ?_
    calc rs n
    _ = rs (⟨n, by simp [hn]⟩ : Finset.range N) := rfl
    _ ≤ ⨆ n : Finset.range N, rs n := by
      refine le_ciSup (f := fun (x : Finset.range N) ↦ rs x) ?_ (⟨n, by simp [hn]⟩ : Finset.range N)
      exact Finite.bddAbove_range _
    _ ≤ r ⊔ ⨆ n : Finset.range N, rs n := le_max_right _ _
    _ ≤ v := hv
  · have hn_le : N ≤ n := not_lt.mp hn
    specialize h n hn_le
    refine (h_anti n ?_).trans h.le
    calc r
    _ ≤ r ⊔ ⨆ n : Finset.range N, rs n := le_max_left _ _
    _ ≤ v := hv

lemma iSup_set_seq {E : Type*} {_ : MeasurableSpace E} (μ : ℕ → Measure E) {s : Set E} :
    ⨆ μ' ∈ {μ n | n}, μ' s = ⨆ n, μ n s := by
  apply le_antisymm
  · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
    intro n
    exact le_iSup (fun i ↦ μ i s) n
  · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff]
    intro n
    calc μ n s
    _ ≤ ⨆ i, ⨆ (_ : μ i = μ n), μ i s := le_biSup (fun i ↦ μ i s) rfl
    _ = ⨆ i, ⨆ (_ : μ i = μ n), μ n s := by
      convert rfl using 4 with m hm
      rw [hm]
    _ ≤ ⨆ μ', ⨆ i, ⨆ (_ : μ i = μ'), μ' s :=
      le_iSup (fun μ' ↦ ⨆ i, ⨆ (_ : μ i = μ'), μ' s) (μ n)

section NormedSpace

lemma tendsto_measure_norm_gt_of_isTightMeasureSet (hS : IsTightMeasureSet S) :
    Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) := by
  suffices Tendsto ((⨆ μ ∈ S, μ) ∘ (fun r ↦ {x | r < ‖x‖})) atTop (𝓝 0) by
    convert this with r
    simp
  refine hS.comp ?_
  simp only [tendsto_smallSets_iff, mem_cocompact, eventually_atTop, ge_iff_le, forall_exists_index,
    and_imp]
  intro s t ht_compact hts
  rcases Set.eq_empty_or_nonempty t with rfl | ht_nonempty
  · simp only [Set.compl_empty, Set.univ_subset_iff] at hts
    simp [hts]
  obtain ⟨r, h_subset⟩ : ∃ r, t ⊆ {x | ‖x‖ ≤ r} := by
    obtain ⟨xmax, _, hxmax⟩ : ∃ x ∈ t, IsMaxOn (fun x ↦ ‖x‖) t x :=
      ht_compact.exists_isMaxOn (f := fun x : E ↦ ‖x‖) ht_nonempty (by fun_prop)
    exact ⟨‖xmax‖, fun x hxK ↦ hxmax hxK⟩
  refine ⟨r, fun u hu ↦ subset_trans ?_ hts⟩
  simp_rw [← not_le]
  refine Set.compl_subset_compl.mp ?_
  simp only [compl_compl, not_le]
  refine h_subset.trans fun x ↦ ?_
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
  exact fun hx ↦ hx.trans hu

section FiniteDimensional

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma isTightMeasureSet_of_tendsto_measure_norm_gt
    (h : Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  refine IsTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
  rw [ENNReal.tendsto_atTop_zero] at h
  obtain ⟨r, h⟩ := h ε hε
  refine ⟨Metric.closedBall 0 r, isCompact_closedBall 0 r, ?_⟩
  specialize h r le_rfl
  simp only [iSup_le_iff] at h
  convert h using 4 with μ hμ
  ext
  simp

/-- In a finite dimensional real normed space, a set of measures `S` is tight if and only if
the function `r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}` tends to `0` at infinity. -/
lemma isTightMeasureSet_iff_tendsto_measure_norm_gt :
    IsTightMeasureSet S ↔ Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖}) atTop (𝓝 0) :=
  ⟨tendsto_measure_norm_gt_of_isTightMeasureSet, isTightMeasureSet_of_tendsto_measure_norm_gt⟩

lemma isTightMeasureSet_of_tendsto_limsup_measure_norm_gt [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
    (h : Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet {μ n | n} := by
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  convert tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) h fun n u v huv ↦ ?_ with y
  · exact iSup_set_seq μ
  · have h_tight : IsTightMeasureSet {μ n} :=
      isTightMeasureSet_singleton_of_innerRegularWRT
        (innerRegular_isCompact_isClosed_measurableSet_of_finite (μ n))
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
    simpa using h_tight
  · refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    exact huv.trans_lt hx

lemma isTightMeasureSet_iff_tendsto_limsup_measure_norm_gt [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)] :
    IsTightMeasureSet {μ n | n}
      ↔ Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < ‖x‖}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h ↦ ?_, isTightMeasureSet_of_tendsto_limsup_measure_norm_gt⟩
  have h_sup := tendsto_measure_norm_gt_of_isTightMeasureSet h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_sup (fun _ ↦ zero_le') ?_
  intro r
  simp_rw [iSup_set_seq]
  exact limsup_le_iSup

end FiniteDimensional

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma norm_le_mul_iSup_abs_inner (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ≤ √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim x 0
    simp [this]
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simp only [← Module.finrank_eq_card_basis b.toBasis, Nat.cast_pos, Module.finrank_pos_iff]
    infer_instance
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  calc ‖x‖
  _ = √(∑ i, ⟪b i, x⟫ ^ 2) := by
    simp_rw [norm_eq_sqrt_real_inner, ← OrthonormalBasis.sum_inner_mul_inner b x x,
      real_inner_comm _ x, ← pow_two]
  _ = √(∑ i, |⟪b i, x⟫| ^ 2) := by simp
  _ ≤ √(∑ _ : ι, (⨆ j, |⟪b j, x⟫|) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j ↦ |⟪b j, x⟫|) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    exact le_ciSup_of_le (by simp) (Nonempty.some this) (by positivity)

lemma isTightMeasureSet_of_forall_basis_tendsto (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < |⟪b i, x⟫|}) atTop (𝓝 0)) :
    IsTightMeasureSet S := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp only [IsTightMeasureSet, cocompact_eq_bot, smallSets_bot]
    convert tendsto_pure_nhds (a := ∅) _
    simp
  have h_rank : (0 : ℝ) < Fintype.card ι := by
    simp only [← Module.finrank_eq_card_basis b.toBasis, Nat.cast_pos, Module.finrank_pos_iff]
    infer_instance
  have : Nonempty ι := by simpa [Fintype.card_pos_iff] using h_rank
  refine isTightMeasureSet_of_tendsto_measure_norm_gt ?_
  have h_le : (fun r ↦ ⨆ μ ∈ S, μ {x | r < ‖x‖})
      ≤ fun r ↦ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
    intro r
    calc ⨆ μ ∈ S, μ {x | r < ‖x‖}
    _ ≤ ⨆ μ ∈ S, μ (⋃ i, {x : E | r / √(Fintype.card ι) < |⟪b i, x⟫|}) := by
      gcongr with μ hμS
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hx ⊢
      have hx' : r < √(Fintype.card ι) * ⨆ i, |⟪b i, x⟫| :=
        hx.trans_le (norm_le_mul_iSup_abs_inner b x)
      rw [← div_lt_iff₀' (by positivity)] at hx'
      by_contra! h_le
      exact lt_irrefl (r / √(Fintype.card ι)) (hx'.trans_le (ciSup_le h_le))
    _ ≤ ⨆ μ ∈ S, ∑ i, μ {x : E | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
      gcongr with μ hμS
      exact measure_iUnion_fintype_le μ _
    _ ≤ ∑ i, ⨆ μ ∈ S, μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|} := by
      refine iSup_le fun μ ↦ (iSup_le fun hμS ↦ ?_)
      gcongr with i
      exact le_biSup (fun μ ↦ μ {x | r / √(Fintype.card ι) < |⟪b i, x⟫|}) hμS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le') h_le
  have : ∑ i : ι, (0 : ℝ≥0∞) = 0 := by simp
  rw [← this]
  refine tendsto_finset_sum Finset.univ fun i _ ↦ ?_
  refine (h i).comp ?_
  exact Tendsto.atTop_div_const (by positivity) tendsto_id

lemma isTightMeasureSet_iff_forall_basis_tendsto (b : OrthonormalBasis ι ℝ E) :
    IsTightMeasureSet S
      ↔ ∀ i, Tendsto (fun r : ℝ ↦ ⨆ μ ∈ S, μ {x | r < |⟪b i, x⟫|}) atTop (𝓝 0) := by
  refine ⟨fun h i ↦ ?_, isTightMeasureSet_of_forall_basis_tendsto b⟩
  rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le') ?_
  intro r
  have h_le (μ : Measure E) : μ {x | r < |⟪b i, x⟫|} ≤ μ {x | r < ‖x‖} := by
    refine measure_mono fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq] at hx ⊢
    refine hx.trans_le ?_
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp
  simp only [iSup_le_iff]
  intro μ hμS
  refine le_iSup_of_le (i := μ) ?_
  simp only [hμS, iSup_pos]
  exact h_le μ

lemma isTightMeasureSet_of_forall_basis_tendsto_limsup [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)] (b : OrthonormalBasis ι ℝ E)
    (h : ∀ i, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < |⟪b i, x⟫|}) atTop) atTop (𝓝 0)) :
    IsTightMeasureSet {μ n | n} := by
  refine isTightMeasureSet_of_forall_basis_tendsto b fun i ↦ ?_
  convert tendsto_iSup_of_tendsto_limsup (fun n ↦ ?_) (h i) fun n u v huv ↦ ?_ with y
  · apply le_antisymm
    · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff, forall_apply_eq_imp_iff]
      exact fun n ↦ le_iSup (fun j ↦ μ j {x | y < |⟪b i, x⟫|}) n
    · simp only [Set.mem_setOf_eq, iSup_exists, iSup_le_iff]
      intro n
      calc μ n {x | y < |⟪b i, x⟫|}
      _ ≤ ⨆ j, ⨆ (_ : μ j = μ n), μ j {x | y < |⟪b i, x⟫|} :=
          le_biSup (fun j ↦ μ j {x | y < |⟪b i, x⟫|}) rfl
      _ = ⨆ j, ⨆ (_ : μ j = μ n), μ n {x | y < |⟪b i, x⟫|} := by
        convert rfl using 4 with m hm
        rw [hm]
      _ ≤ ⨆ μ', ⨆ j, ⨆ (_ : μ j = μ'), μ' {x | y < |⟪b i, x⟫|} :=
        le_iSup (fun μ' ↦ ⨆ j, ⨆ (_ : μ j = μ'), μ' {x | y < |⟪b i, x⟫|}) (μ n)
  · have h_tight : IsTightMeasureSet {(μ n).map (fun x ↦ ⟪b i, x⟫)} :=
      isTightMeasureSet_singleton
    rw [isTightMeasureSet_iff_tendsto_measure_norm_gt] at h_tight
    have h_map r : (μ n).map (fun x ↦ inner ((b) i) x) {x | r < |x|}
        = μ n {x | r < |⟪b i, x⟫|} := by
      rw [Measure.map_apply (by fun_prop)]
      · simp
      · exact MeasurableSet.preimage measurableSet_Ioi (by fun_prop)
    simpa [h_map] using h_tight
  · exact measure_mono fun x hx ↦ huv.trans_lt hx

lemma isTightMeasureSet_iff_forall_basis_tendsto_limsup [BorelSpace E]
    {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)] (b : OrthonormalBasis ι ℝ E) :
    IsTightMeasureSet {μ n | n}
      ↔ ∀ i, Tendsto (fun r : ℝ ↦ limsup (fun n ↦ μ n {x | r < |⟪b i, x⟫|}) atTop) atTop (𝓝 0) := by
  refine ⟨fun h i ↦ ?_, isTightMeasureSet_of_forall_basis_tendsto_limsup b⟩
  rw [isTightMeasureSet_iff_forall_basis_tendsto b] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h i) (fun _ ↦ zero_le') ?_
  intro r
  simp_rw [iSup_set_seq]
  exact limsup_le_iSup

end InnerProductSpace

end MeasureTheory
