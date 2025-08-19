/-
Copyright (c) 2022 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Convergence in measure

We define convergence in measure which is one of the many notions of convergence in probability.
A sequence of functions `f` is said to converge in measure to some function `g`
if for all `ε > 0`, the measure of the set `{x | ε ≤ edist (f i x) (g x)}` tends to 0 as `i`
converges along some given filter `l`.

Convergence in measure is most notably used in the formulation of the weak law of large numbers
and is also useful in theorems such as the Vitali convergence theorem. This file provides some
basic lemmas for working with convergence in measure and establishes some relations between
convergence in measure and other notions of convergence.

## Main definitions

* `MeasureTheory.TendstoInMeasure (μ : Measure α) (f : ι → α → E) (g : α → E)`: `f` converges
  in `μ`-measure to `g`.

## Main results

* `MeasureTheory.tendstoInMeasure_of_tendsto_ae`: convergence almost everywhere in a finite
  measure space implies convergence in measure.
* `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`: if `f` is a sequence of functions
  which converges in measure to `g`, then `f` has a subsequence which convergence almost
  everywhere to `g`.
* `MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff`: for a sequence of functions `f`,
  convergence in measure is equivalent to the fact that every subsequence has another subsequence
  that converges almost surely.
* `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm`: convergence in Lp implies convergence
  in measure.
-/


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory

variable {α ι κ E : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- A sequence of functions `f` is said to converge in measure to some function `g` if for all
`ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i` converges along
some given filter `l`. -/
def TendstoInMeasure [EDist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι → α → E)
    (l : Filter ι) (g : α → E) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i ↦ μ { x | ε ≤ edist (f i x) (g x) }) l (𝓝 0)

lemma tendstoInMeasure_of_ne_top [EDist E] {f : ι → α → E} {l : Filter ι} {g : α → E}
    (h : ∀ ε, 0 < ε → ε ≠ ∞ → Tendsto (fun i ↦ μ { x | ε ≤ edist (f i x) (g x) }) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  by_cases hε_top : ε = ∞
  · have h1 : Tendsto (fun n ↦ μ {ω | 1 ≤ edist (f n ω) (g ω)}) l (𝓝 0) := h 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ ↦ zero_le') ?_
    intro n
    simp only [hε_top]
    gcongr
    simp
  · exact h ε hε hε_top

theorem tendstoInMeasure_iff_enorm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → α → E}
    {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → ε ≠ ∞ → Tendsto (fun i ↦ μ { x | ε ≤ ‖f i x - g x‖ₑ }) l (𝓝 0) := by
  simp_rw [← edist_eq_enorm_sub]
  exact ⟨fun h ε hε hε_top ↦ h ε hε, tendstoInMeasure_of_ne_top⟩

lemma tendstoInMeasure_iff_dist [PseudoMetricSpace E] {f : ι → α → E} {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ f l g
      ↔ ∀ ε, 0 < ε → Tendsto (fun i ↦ μ { x | ε ≤ dist (f i x) (g x) }) l (𝓝 0) := by
  refine ⟨fun h ε hε ↦ ?_, fun h ↦ ?_⟩
  · convert h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) with i a
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  · refine tendstoInMeasure_of_ne_top fun ε hε hε_top ↦ ?_
    convert h ε.toReal (ENNReal.toReal_pos hε.ne' hε_top) with i a
    rw [edist_dist, ENNReal.le_ofReal_iff_toReal_le hε_top (by positivity)]

theorem tendstoInMeasure_iff_norm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → α → E}
    {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i ↦ μ { x | ε ≤ ‖f i x - g x‖ }) l (𝓝 0) := by
  simp_rw [tendstoInMeasure_iff_dist, dist_eq_norm_sub]

theorem tendstoInMeasure_iff_tendsto_toNNReal [EDist E] [IsFiniteMeasure μ]
    {f : ι → α → E} {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i ↦ (μ { x | ε ≤ edist (f i x) (g x) }).toNNReal) l (𝓝 0) := by
  have hfin ε i : μ { x | ε ≤ edist (f i x) (g x) } ≠ ⊤ :=
    measure_ne_top μ {x | ε ≤ edist (f i x) (g x)}
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · have hf : (fun i ↦ (μ { x | ε ≤ edist (f i x) (g x) }).toNNReal) =
        ENNReal.toNNReal ∘ (fun i ↦ (μ { x | ε ≤ edist (f i x) (g x) })) := rfl
    rw [hf, ENNReal.tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · rw [← ENNReal.tendsto_toNNReal_iff ENNReal.zero_ne_top (hfin ε)]
    exact h ε hε

lemma TendstoInMeasure.mono [EDist E] {f : ι → α → E} {g : α → E} {u v : Filter ι} (huv : v ≤ u)
    (hg : TendstoInMeasure μ f u g) : TendstoInMeasure μ f v g :=
  fun ε hε ↦ (hg ε hε).mono_left huv

lemma TendstoInMeasure.comp [EDist E] {f : ι → α → E} {g : α → E} {u : Filter ι}
    {v : Filter κ} {ns : κ → ι} (hg : TendstoInMeasure μ f u g) (hns : Tendsto ns v u) :
    TendstoInMeasure μ (f ∘ ns) v g := fun ε hε ↦ (hg ε hε).comp hns

namespace TendstoInMeasure

variable [EDist E] {l : Filter ι} {f f' : ι → α → E} {g g' : α → E}

protected theorem congr' (h_left : ∀ᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' := by
  intro ε hε
  suffices
    (fun i ↦ μ { x | ε ≤ edist (f' i x) (g' x) }) =ᶠ[l] fun i ↦ μ { x | ε ≤ edist (f i x) (g x) } by
    rw [tendsto_congr' this]
    exact h_tendsto ε hε
  filter_upwards [h_left] with i h_ae_eq
  refine measure_congr ?_
  filter_upwards [h_ae_eq, h_right] with x hxf hxg
  rw [eq_iff_iff]
  change ε ≤ edist (f' i x) (g' x) ↔ ε ≤ edist (f i x) (g x)
  rw [hxg, hxf]

protected theorem congr (h_left : ∀ i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' :=
  TendstoInMeasure.congr' (Eventually.of_forall h_left) h_right h_tendsto

theorem congr_left (h : ∀ i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f' l g :=
  h_tendsto.congr h EventuallyEq.rfl

theorem congr_right (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f l g' :=
  h_tendsto.congr (fun _ ↦ EventuallyEq.rfl) h

end TendstoInMeasure

section ExistsSeqTendstoAe

variable [PseudoEMetricSpace E]
variable {f : ℕ → α → E} {g : α → E}

/-- Auxiliary lemma for `tendstoInMeasure_of_tendsto_ae`. -/
theorem tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable [IsFiniteMeasure μ]
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  refine fun ε hε ↦ ENNReal.tendsto_atTop_zero.mpr fun δ hδ ↦ ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to ℝ≥0 using hδi
  rw [gt_iff_lt, ENNReal.coe_pos, ← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [EMetric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  suffices { x : α | ε ≤ edist (f n x) (g x) } ⊆ t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff, Set.notMem_setOf_iff, edist_comm, not_le]
  exact hN n hn x hx

/-- Convergence a.e. implies convergence in measure in a finite measure space. -/
theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ] (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  refine TendstoInMeasure.congr (fun i ↦ (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable
    (fun i ↦ (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have hf_eq_ae : ∀ᵐ x ∂μ, ∀ n, (hf n).mk (f n) x = f n x :=
    ae_all_iff.mpr fun n ↦ (hf n).ae_eq_mk.symm
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg
  rw [← hxg, funext fun n ↦ hxf n]
  exact hxfg

namespace ExistsSeqTendstoAe

theorem exists_nat_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : ℕ) :
    ∃ N, ∀ m ≥ N, μ { x | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f m x) (g x) } ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  specialize hfg ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.pow_pos (by simp) _)
  rw [ENNReal.tendsto_atTop_zero] at hfg
  exact hfg ((2 : ℝ≥0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr fun h_zero ↦ by simpa using pow_eq_zero h_zero)

/-- Given a sequence of functions `f` which converges in measure to `g`,
`seqTendstoAeSeqAux` is a sequence such that
`∀ m ≥ seqTendstoAeSeqAux n, μ {x | 2⁻¹ ^ n ≤ dist (f m x) (g x)} ≤ 2⁻¹ ^ n`. -/
noncomputable def seqTendstoAeSeqAux (hfg : TendstoInMeasure μ f atTop g) (n : ℕ) :=
  Classical.choose (exists_nat_measure_lt_two_inv hfg n)

/-- Transformation of `seqTendstoAeSeqAux` to makes sure it is strictly monotone. -/
noncomputable def seqTendstoAeSeq (hfg : TendstoInMeasure μ f atTop g) : ℕ → ℕ
  | 0 => seqTendstoAeSeqAux hfg 0
  | n + 1 => max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq hfg n + 1)

theorem seqTendstoAeSeq_succ (hfg : TendstoInMeasure μ f atTop g) {n : ℕ} :
    seqTendstoAeSeq hfg (n + 1) =
      max (seqTendstoAeSeqAux hfg (n + 1)) (seqTendstoAeSeq hfg n + 1) := by
  rw [seqTendstoAeSeq]

theorem seqTendstoAeSeq_spec (hfg : TendstoInMeasure μ f atTop g) (n k : ℕ)
    (hn : seqTendstoAeSeq hfg n ≤ k) :
    μ { x | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (f k x) (g x) } ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  cases n
  · exact Classical.choose_spec (exists_nat_measure_lt_two_inv hfg 0) k hn
  · exact Classical.choose_spec
      (exists_nat_measure_lt_two_inv hfg _) _ (le_trans (le_max_left _ _) hn)

theorem seqTendstoAeSeq_strictMono (hfg : TendstoInMeasure μ f atTop g) :
    StrictMono (seqTendstoAeSeq hfg) := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  rw [seqTendstoAeSeq_succ]
  exact lt_of_lt_of_le (lt_add_one <| seqTendstoAeSeq hfg n) (le_max_right _ _)

end ExistsSeqTendstoAe

/-- If `f` is a sequence of functions which converges in measure to `g`, then there exists a
subsequence of `f` which converges a.e. to `g`. -/
theorem TendstoInMeasure.exists_seq_tendsto_ae (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun i ↦ f (ns i) x) atTop (𝓝 (g x)) := by
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
    `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
    `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by the
    first Borel-Cantelli lemma.

    On the other hand, as `s` is precisely the set for which `f (ns k)`
    doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real (ε : ℝ≥0∞) (hε : 0 < ε) : ∃ k : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ k < ε := by
    obtain ⟨k, h_k⟩ : ∃ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
    · positivity
    · simp
  set ns := ExistsSeqTendstoAe.seqTendstoAeSeq hfg
  use ns
  let S := fun k ↦ { x | (2 : ℝ≥0∞)⁻¹ ^ k ≤ edist (f (ns k) x) (g x) }
  have hμS_le : ∀ k, μ (S k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    fun k ↦ ExistsSeqTendstoAe.seqTendstoAeSeq_spec hfg k (ns k) le_rfl
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have h_tendsto : ∀ x ∈ sᶜ, Tendsto (fun i ↦ f (ns i) x) atTop (𝓝 (g x)) := by
    refine fun x hx ↦ EMetric.tendsto_atTop.mpr fun ε hε ↦ ?_
    rw [hs, limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter, Set.compl_iUnion,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
    obtain ⟨N, hNx⟩ := hx
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max N (k - 1), fun n hn_ge ↦ lt_of_le_of_lt ?_ hk_lt_ε⟩
    specialize hNx n ((le_max_left _ _).trans hn_ge)
    have h_inv_n_le_k : (2 : ℝ≥0∞)⁻¹ ^ n ≤ 2 * (2 : ℝ≥0∞)⁻¹ ^ k := by
      nth_rw 2 [← pow_one (2 : ℝ≥0∞)]
      rw [mul_comm, ← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.inv_le_iff_le_mul, ← mul_assoc,
        mul_comm (_ ^ n), mul_assoc, ← ENNReal.inv_le_iff_le_mul, inv_inv, ← pow_add]
      · gcongr
        · norm_num
        · omega
      all_goals simp
    exact le_trans hNx.le h_inv_n_le_k
  rw [ae_iff]
  refine ⟨ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono hfg, measure_mono_null (fun x ↦ ?_) hμs⟩
  rw [Set.mem_setOf_eq, ← @Classical.not_not (x ∈ s), not_imp_not]
  exact h_tendsto x

theorem TendstoInMeasure.exists_seq_tendstoInMeasure_atTop {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ ns : ℕ → ι, Tendsto ns atTop u ∧ TendstoInMeasure μ (fun n ↦ f (ns n)) atTop g := by
  obtain ⟨ns, h_tendsto_ns⟩ : ∃ ns : ℕ → ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε ↦ (hfg ε hε).comp h_tendsto_ns⟩

theorem TendstoInMeasure.exists_seq_tendsto_ae' {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ ns : ℕ → ι, Tendsto ns atTop u ∧ ∀ᵐ x ∂μ, Tendsto (fun i ↦ f (ns i) x) atTop (𝓝 (g x)) := by
  obtain ⟨ms, hms1, hms2⟩ := hfg.exists_seq_tendstoInMeasure_atTop
  obtain ⟨ns, hns1, hns2⟩ := hms2.exists_seq_tendsto_ae
  exact ⟨ms ∘ ns, hms1.comp hns1.tendsto_atTop, hns2⟩

/-- `TendstoInMeasure` is equivalent to every subsequence having another subsequence
 which converges almost surely. -/
theorem exists_seq_tendstoInMeasure_atTop_iff [IsFiniteMeasure μ]
    {f : ℕ → α → E} (hf : ∀ (n : ℕ), AEStronglyMeasurable (f n) μ) {g : α → E} :
    TendstoInMeasure μ f atTop g ↔
      ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ (ω : α) ∂μ, Tendsto (fun i ↦ f (ns (ns' i)) ω) atTop (𝓝 (g ω)) := by
  refine ⟨fun hfg _ hns ↦ (hfg.comp hns.tendsto_atTop).exists_seq_tendsto_ae,
    not_imp_not.mp (fun h1 ↦ ?_)⟩
  rw [tendstoInMeasure_iff_tendsto_toNNReal] at h1
  push_neg at *
  obtain ⟨ε, hε, h2⟩ := h1
  obtain ⟨δ, ns, hδ, hns, h3⟩ : ∃ (δ : ℝ≥0) (ns : ℕ → ℕ), 0 < δ ∧ StrictMono ns ∧
      ∀ n, δ ≤ (μ {x | ε ≤ edist (f (ns n) x) (g x)}).toNNReal := by
    obtain ⟨s, hs, h4⟩ := not_tendsto_iff_exists_frequently_notMem.1 h2
    obtain ⟨δ, hδ, h5⟩ := NNReal.nhds_zero_basis.mem_iff.1 hs
    obtain ⟨ns, hns, h6⟩ := extraction_of_frequently_atTop h4
    exact ⟨δ, ns, hδ, hns, fun n ↦ Set.notMem_Iio.1 (Set.notMem_subset h5 (h6 n))⟩
  refine ⟨ns, hns, fun ns' _ ↦ ?_⟩
  by_contra h6
  have h7 := tendstoInMeasure_iff_tendsto_toNNReal.mp <|
    tendstoInMeasure_of_tendsto_ae (fun n ↦ hf _) h6
  exact lt_irrefl _ (lt_of_le_of_lt (ge_of_tendsto' (h7 ε hε) (fun n ↦ h3 _)) hδ)

end ExistsSeqTendstoAe

section TendstoInMeasureUnique

/-- The limit in measure is ae unique. -/
theorem tendstoInMeasure_ae_unique [EMetricSpace E] {g h : α → E} {f : ι → α → E} {u : Filter ι}
    [NeBot u] [IsCountablyGenerated u] (hg : TendstoInMeasure μ f u g)
    (hh : TendstoInMeasure μ f u h) : g =ᵐ[μ] h := by
  obtain ⟨ns, h1, h1'⟩ := hg.exists_seq_tendsto_ae'
  obtain ⟨ns', h2, h2'⟩ := (hh.comp h1).exists_seq_tendsto_ae'
  filter_upwards [h1', h2'] with ω hg1 hh1
  exact tendsto_nhds_unique (hg1.comp h2) hh1

end TendstoInMeasureUnique

section AEMeasurableOf

variable [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

theorem TendstoInMeasure.aemeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n ↦ hf (ns n)) hns

end AEMeasurableOf

section TendstoInMeasureOf

variable [NormedAddCommGroup E] {p : ℝ≥0∞}
variable {f : ι → α → E} {g : α → E}

/-- This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` where we
allow `p = ∞` and only require `AEStronglyMeasurable`. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    {l : Filter ι} (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_ne_top fun ε hε hε_top ↦ ?_
  replace hfg := ENNReal.Tendsto.const_mul (a := 1 / ε ^ p.toReal)
    (Tendsto.ennrpow_const p.toReal hfg) (Or.inr <| by simp [hε.ne'])
  simp only [mul_zero,
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro δ hδ
  refine (hfg δ hδ).mono fun n hn ↦ ?_
  refine le_trans ?_ hn
  rw [one_div, ← ENNReal.inv_mul_le_iff, inv_inv]
  · convert mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top
      ((hf n).sub hg).aestronglyMeasurable ε using 6
    simp [edist_eq_enorm_sub]
  · simp [hε_top]
  · simp [hε.ne']

/-- This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` where we
allow `p = ∞`. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ) {l : Filter ι}
    (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  refine TendstoInMeasure.congr (fun i ↦ (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    hp_ne_zero hp_ne_top (fun i ↦ (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have : (fun n ↦ eLpNorm ((hf n).mk (f n) - hg.mk g) p μ) = fun n ↦ eLpNorm (f n - g) p μ := by
    ext1 n; refine eLpNorm_congr_ae (EventuallyEq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm)
  rw [this]
  exact hfg

/-- See also `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` which work for general
Lp-convergence for all `p ≠ 0`. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm_top {E} [NormedAddCommGroup E] {f : ι → α → E}
    {g : α → E} {l : Filter ι} (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) ∞ μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  refine tendstoInMeasure_of_ne_top fun δ hδ hδ_top ↦ ?_
  simp only [eLpNorm_exponent_top, eLpNormEssSup] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro ε hε
  specialize hfg (δ / 2) (ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩)
  refine hfg.mono fun n hn ↦ ?_
  simp only [Pi.sub_apply] at *
  have : essSup (fun x : α ↦ ‖f n x - g x‖ₑ) μ < δ :=
    hn.trans_lt (ENNReal.half_lt_self hδ.ne' hδ_top)
  refine ((le_of_eq ?_).trans (ae_lt_of_essSup_lt this).le).trans hε.le
  congr with x
  simp [edist_eq_enorm_sub]

/-- Convergence in Lp implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm {l : Filter ι} (hp_ne_zero : p ≠ 0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hfg : Tendsto (fun n ↦ eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    exact tendstoInMeasure_of_tendsto_eLpNorm_top hfg
  · exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg

/-- Convergence in Lp implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_Lp [hp : Fact (1 ≤ p)] {f : ι → Lp E p μ} {g : Lp E p μ}
    {l : Filter ι} (hfg : Tendsto f l (𝓝 g)) : TendstoInMeasure μ (fun n ↦ f n) l g :=
  tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hp.elim).ne.symm
    (fun _ ↦ Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hfg)

end TendstoInMeasureOf

end MeasureTheory
