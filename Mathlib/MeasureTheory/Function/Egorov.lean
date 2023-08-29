/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

#align_import measure_theory.function.egorov from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Egorov theorem

This file contains the Egorov theorem which states that an almost everywhere convergent
sequence on a finite measure space converges uniformly except on an arbitrarily small set.
This theorem is useful for the Vitali convergence theorem as well as theorems regarding
convergence in measure.

## Main results

* `MeasureTheory.Egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/


noncomputable section

open Classical MeasureTheory NNReal ENNReal Topology

namespace MeasureTheory

open Set Filter TopologicalSpace

variable {α β ι : Type*} {m : MeasurableSpace α} [MetricSpace β] {μ : Measure α}

namespace Egorov

/-- Given a sequence of functions `f` and a function `g`, `notConvergentSeq f g n j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (n + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeq [Preorder ι] (f : ι → α → β) (g : α → β) (n : ℕ) (j : ι) : Set α :=
  ⋃ (k) (_ : j ≤ k), { x | 1 / (n + 1 : ℝ) < dist (f k x) (g x) }
#align measure_theory.egorov.not_convergent_seq MeasureTheory.Egorov.notConvergentSeq

variable {n : ℕ} {i j : ι} {s : Set α} {ε : ℝ} {f : ι → α → β} {g : α → β}

theorem mem_notConvergentSeq_iff [Preorder ι] {x : α} :
    x ∈ notConvergentSeq f g n j ↔ ∃ (k : _) (_ : j ≤ k), 1 / (n + 1 : ℝ) < dist (f k x) (g x) := by
  simp_rw [notConvergentSeq, Set.mem_iUnion]
  -- ⊢ (∃ i i_1, x ∈ {x | 1 / (↑n + 1) < dist (f i x) (g x)}) ↔ ∃ k x_1, 1 / (↑n +  …
  rfl
  -- 🎉 no goals
#align measure_theory.egorov.mem_not_convergent_seq_iff MeasureTheory.Egorov.mem_notConvergentSeq_iff

theorem notConvergentSeq_antitone [Preorder ι] : Antitone (notConvergentSeq f g n) :=
  fun _ _ hjk => Set.iUnion₂_mono' fun l hl => ⟨l, le_trans hjk hl, Set.Subset.rfl⟩
#align measure_theory.egorov.not_convergent_seq_antitone MeasureTheory.Egorov.notConvergentSeq_antitone

theorem measure_inter_notConvergentSeq_eq_zero [SemilatticeSup ι] [Nonempty ι]
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ ⋂ j, notConvergentSeq f g n j) = 0 := by
  simp_rw [Metric.tendsto_atTop, ae_iff] at hfg
  -- ⊢ ↑↑μ (s ∩ ⋂ (j : ι), notConvergentSeq f g n j) = 0
  rw [← nonpos_iff_eq_zero, ← hfg]
  -- ⊢ ↑↑μ (s ∩ ⋂ (j : ι), notConvergentSeq f g n j) ≤ ↑↑μ {a | ¬(a ∈ s → ∀ (ε : ℝ) …
  refine' measure_mono fun x => _
  -- ⊢ x ∈ s ∩ ⋂ (j : ι), notConvergentSeq f g n j → x ∈ {a | ¬(a ∈ s → ∀ (ε : ℝ),  …
  simp only [Set.mem_inter_iff, Set.mem_iInter, ge_iff_le, mem_notConvergentSeq_iff]
  -- ⊢ (x ∈ s ∧ ∀ (i : ι), ∃ k x_1, 1 / (↑n + 1) < dist (f k x) (g x)) → x ∈ {a | ¬ …
  push_neg
  -- ⊢ (x ∈ s ∧ ∀ (i : ι), ∃ k x_1, 1 / (↑n + 1) < dist (f k x) (g x)) → x ∈ {a | a …
  rintro ⟨hmem, hx⟩
  -- ⊢ x ∈ {a | a ∈ s ∧ ∃ ε, ε > 0 ∧ ∀ (N : ι), ∃ n, N ≤ n ∧ ε ≤ dist (f n a) (g a)}
  refine' ⟨hmem, 1 / (n + 1 : ℝ), Nat.one_div_pos_of_nat, fun N => _⟩
  -- ⊢ ∃ n_1, N ≤ n_1 ∧ 1 / (↑n + 1) ≤ dist (f n_1 x) (g x)
  obtain ⟨n, hn₁, hn₂⟩ := hx N
  -- ⊢ ∃ n, N ≤ n ∧ 1 / (↑n✝ + 1) ≤ dist (f n x) (g x)
  exact ⟨n, hn₁, hn₂.le⟩
  -- 🎉 no goals
#align measure_theory.egorov.measure_inter_not_convergent_seq_eq_zero MeasureTheory.Egorov.measure_inter_notConvergentSeq_eq_zero

theorem notConvergentSeq_measurableSet [Preorder ι] [Countable ι]
    (hf : ∀ n, StronglyMeasurable[m] (f n)) (hg : StronglyMeasurable g) :
    MeasurableSet (notConvergentSeq f g n j) :=
  MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ =>
      StronglyMeasurable.measurableSet_lt stronglyMeasurable_const <| (hf k).dist hg
#align measure_theory.egorov.not_convergent_seq_measurable_set MeasureTheory.Egorov.notConvergentSeq_measurableSet

theorem measure_notConvergentSeq_tendsto_zero [SemilatticeSup ι] [Countable ι]
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    Tendsto (fun j => μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 0) := by
  cases' isEmpty_or_nonempty ι with h h
  -- ⊢ Tendsto (fun j => ↑↑μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 0)
  · have : (fun j => μ (s ∩ notConvergentSeq f g n j)) = fun j => 0 := by
      simp only [eq_iff_true_of_subsingleton]
    rw [this]
    -- ⊢ Tendsto (fun j => 0) atTop (𝓝 0)
    exact tendsto_const_nhds
    -- 🎉 no goals
  rw [← measure_inter_notConvergentSeq_eq_zero hfg n, Set.inter_iInter]
  -- ⊢ Tendsto (fun j => ↑↑μ (s ∩ notConvergentSeq f g n j)) atTop (𝓝 (↑↑μ (⋂ (i :  …
  refine' tendsto_measure_iInter (fun n => hsm.inter <| notConvergentSeq_measurableSet hf hg)
    (fun k l hkl => Set.inter_subset_inter_right _ <| notConvergentSeq_antitone hkl)
    ⟨h.some,
      (lt_of_le_of_lt (measure_mono <| Set.inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).ne⟩
#align measure_theory.egorov.measure_not_convergent_seq_tendsto_zero MeasureTheory.Egorov.measure_notConvergentSeq_tendsto_zero

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι]

theorem exists_notConvergentSeq_lt (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    ∃ j : ι, μ (s ∩ notConvergentSeq f g n j) ≤ ENNReal.ofReal (ε * 2⁻¹ ^ n) := by
  have ⟨N, hN⟩ := (ENNReal.tendsto_atTop ENNReal.zero_ne_top).1
    (measure_notConvergentSeq_tendsto_zero hf hg hsm hs hfg n) (ENNReal.ofReal (ε * 2⁻¹ ^ n)) (by
      rw [gt_iff_lt, ENNReal.ofReal_pos]
      exact mul_pos hε (pow_pos (by norm_num) n))
  rw [zero_add] at hN
  -- ⊢ ∃ j, ↑↑μ (s ∩ notConvergentSeq f g n j) ≤ ENNReal.ofReal (ε * 2⁻¹ ^ n)
  exact ⟨N, (hN N le_rfl).2⟩
  -- 🎉 no goals
#align measure_theory.egorov.exists_not_convergent_seq_lt MeasureTheory.Egorov.exists_notConvergentSeq_lt

/-- Given some `ε > 0`, `notConvergentSeqLTIndex` provides the index such that
`notConvergentSeq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ n`.

This definition is useful for Egorov's theorem. -/
def notConvergentSeqLTIndex (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) : ι :=
  Classical.choose <| exists_notConvergentSeq_lt hε hf hg hsm hs hfg n
#align measure_theory.egorov.not_convergent_seq_lt_index MeasureTheory.Egorov.notConvergentSeqLTIndex

theorem notConvergentSeqLTIndex_spec (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) (n : ℕ) :
    μ (s ∩ notConvergentSeq f g n (notConvergentSeqLTIndex hε hf hg hsm hs hfg n)) ≤
      ENNReal.ofReal (ε * 2⁻¹ ^ n) :=
  Classical.choose_spec <| exists_notConvergentSeq_lt hε hf hg hsm hs hfg n
#align measure_theory.egorov.not_convergent_seq_lt_index_spec MeasureTheory.Egorov.notConvergentSeqLTIndex_spec

/-- Given some `ε > 0`, `iUnionNotConvergentSeq` is the union of `notConvergentSeq` with
specific indices such that `iUnionNotConvergentSeq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def iUnionNotConvergentSeq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Set α :=
  ⋃ n, s ∩ notConvergentSeq f g n (notConvergentSeqLTIndex (half_pos hε) hf hg hsm hs hfg n)
#align measure_theory.egorov.Union_not_convergent_seq MeasureTheory.Egorov.iUnionNotConvergentSeq

theorem iUnionNotConvergentSeq_measurableSet (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableSet <| iUnionNotConvergentSeq hε hf hg hsm hs hfg :=
  MeasurableSet.iUnion fun _ => hsm.inter <| notConvergentSeq_measurableSet hf hg
#align measure_theory.egorov.Union_not_convergent_seq_measurable_set MeasureTheory.Egorov.iUnionNotConvergentSeq_measurableSet

theorem measure_iUnionNotConvergentSeq (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    μ (iUnionNotConvergentSeq hε hf hg hsm hs hfg) ≤ ENNReal.ofReal ε := by
  refine' le_trans (measure_iUnion_le _) (le_trans
    (ENNReal.tsum_le_tsum <| notConvergentSeqLTIndex_spec (half_pos hε) hf hg hsm hs hfg) _)
  simp_rw [ENNReal.ofReal_mul (half_pos hε).le]
  -- ⊢ ∑' (a : ℕ), ENNReal.ofReal (ε / 2) * ENNReal.ofReal (2⁻¹ ^ a) ≤ ENNReal.ofRe …
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg, inv_eq_one_div, tsum_geometric_two,
    ← ENNReal.ofReal_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero]
  · exact fun n => pow_nonneg (by norm_num) _
    -- 🎉 no goals
  · rw [inv_eq_one_div]
    -- ⊢ Summable fun i => (1 / 2) ^ i
    exact summable_geometric_two
    -- 🎉 no goals
#align measure_theory.egorov.measure_Union_not_convergent_seq MeasureTheory.Egorov.measure_iUnionNotConvergentSeq

theorem iUnionNotConvergentSeq_subset (hε : 0 < ε) (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    iUnionNotConvergentSeq hε hf hg hsm hs hfg ⊆ s := by
  rw [iUnionNotConvergentSeq, ← Set.inter_iUnion]
  -- ⊢ s ∩ ⋃ (i : ℕ), notConvergentSeq (fun n => f n) g i (notConvergentSeqLTIndex  …
  exact Set.inter_subset_left _ _
  -- 🎉 no goals
#align measure_theory.egorov.Union_not_convergent_seq_subset MeasureTheory.Egorov.iUnionNotConvergentSeq_subset

theorem tendstoUniformlyOn_diff_iUnionNotConvergentSeq (hε : 0 < ε)
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g) (hsm : MeasurableSet s)
    (hs : μ s ≠ ∞) (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    TendstoUniformlyOn f g atTop (s \ Egorov.iUnionNotConvergentSeq hε hf hg hsm hs hfg) := by
  rw [Metric.tendstoUniformlyOn_iff]
  -- ⊢ ∀ (ε_1 : ℝ), ε_1 > 0 → ∀ᶠ (n : ι) in atTop, ∀ (x : α), x ∈ s \ iUnionNotConv …
  intro δ hδ
  -- ⊢ ∀ᶠ (n : ι) in atTop, ∀ (x : α), x ∈ s \ iUnionNotConvergentSeq hε hf hg hsm  …
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  -- ⊢ ∀ᶠ (n : ι) in atTop, ∀ (x : α), x ∈ s \ iUnionNotConvergentSeq hε hf hg hsm  …
  rw [eventually_atTop]
  -- ⊢ ∃ a, ∀ (b : ι), b ≥ a → ∀ (x : α), x ∈ s \ iUnionNotConvergentSeq hε hf hg h …
  refine' ⟨Egorov.notConvergentSeqLTIndex (half_pos hε) hf hg hsm hs hfg N, fun n hn x hx => _⟩
  -- ⊢ dist (g x) (f n x) < δ
  simp only [Set.mem_diff, Egorov.iUnionNotConvergentSeq, not_exists, Set.mem_iUnion,
    Set.mem_inter_iff, not_and, exists_and_left] at hx
  obtain ⟨hxs, hx⟩ := hx
  -- ⊢ dist (g x) (f n x) < δ
  specialize hx hxs N
  -- ⊢ dist (g x) (f n x) < δ
  rw [Egorov.mem_notConvergentSeq_iff] at hx
  -- ⊢ dist (g x) (f n x) < δ
  push_neg at hx
  -- ⊢ dist (g x) (f n x) < δ
  rw [dist_comm]
  -- ⊢ dist (f n x) (g x) < δ
  exact lt_of_le_of_lt (hx n hn) hN
  -- 🎉 no goals
#align measure_theory.egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq MeasureTheory.Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeq

end Egorov

variable [SemilatticeSup ι] [Nonempty ι] [Countable ι] {γ : Type*} [TopologicalSpace γ]
  {f : ι → α → β} {g : α → β} {s : Set α}

/-- **Egorov's theorem**: If `f : ι → α → β` is a sequence of strongly measurable functions that
converges to `g : α → β` almost everywhere on a measurable set `s` of finite measure,
then for all `ε > 0`, there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g`
uniformly on `s \ t`. We require the index type `ι` to be countable, and usually `ι = ℕ`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendstoUniformlyOn_of_ae_tendsto (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
    ∃ (t : _) (_ : t ⊆ s),
      MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) :=
  ⟨Egorov.iUnionNotConvergentSeq hε hf hg hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_subset hε hf hg hsm hs hfg,
    Egorov.iUnionNotConvergentSeq_measurableSet hε hf hg hsm hs hfg,
    Egorov.measure_iUnionNotConvergentSeq hε hf hg hsm hs hfg,
    Egorov.tendstoUniformlyOn_diff_iUnionNotConvergentSeq hε hf hg hsm hs hfg⟩
#align measure_theory.tendsto_uniformly_on_of_ae_tendsto MeasureTheory.tendstoUniformlyOn_of_ae_tendsto

/-- Egorov's theorem for finite measure spaces. -/
theorem tendstoUniformlyOn_of_ae_tendsto' [IsFiniteMeasure μ] (hf : ∀ n, StronglyMeasurable (f n))
    (hg : StronglyMeasurable g) (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ := by
  have ⟨t, _, ht, htendsto⟩ := tendstoUniformlyOn_of_ae_tendsto hf hg MeasurableSet.univ
    (measure_ne_top μ Set.univ) (by filter_upwards [hfg] with _ htendsto _ using htendsto) hε
  refine' ⟨_, ht, _⟩
  -- ⊢ ↑↑μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop tᶜ
  rwa [Set.compl_eq_univ_diff]
  -- 🎉 no goals
#align measure_theory.tendsto_uniformly_on_of_ae_tendsto' MeasureTheory.tendstoUniformlyOn_of_ae_tendsto'

end MeasureTheory
