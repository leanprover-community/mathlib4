/-
Copyright (c) 2022 Rémy Degenne, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Function.LpSpace

/-!
# Convergence in measure

We define convergence in measure which is one of the many notions of convergence in probability.
A sequence of functions `f` is said to converge in measure to some function `g`
if for all `ε > 0`, the measure of the set `{x | ε ≤ dist (f i x) (g x)}` tends to 0 as `i`
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
def TendstoInMeasure [Dist E] {_ : MeasurableSpace α} (μ : Measure α) (f : ι → α → E) (l : Filter ι)
    (g : α → E) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ dist (f i x) (g x) }) l (𝓝 0)

theorem tendstoInMeasure_iff_norm [SeminormedAddCommGroup E] {l : Filter ι} {f : ι → α → E}
    {g : α → E} :
    TendstoInMeasure μ f l g ↔
      ∀ ε, 0 < ε → Tendsto (fun i => μ { x | ε ≤ ‖f i x - g x‖ }) l (𝓝 0) := by
  simp_rw [TendstoInMeasure, dist_eq_norm]

theorem tendstoInMeasure_iff_tendsto_toNNReal [Dist E] {_ : MeasurableSpace α} {μ : Measure α}
    [hfin: MeasureTheory.IsFiniteMeasure μ] {f : ι → α → E} {l : Filter ι} {g : α → E} :
    TendstoInMeasure μ f l g ↔ ∀ ε, 0 < ε → Tendsto (fun i =>
    (μ { x | ε ≤ dist (f i x) (g x) }).toNNReal) l (𝓝 0) := by
  have hfin : ∀ ε, ∀ i, μ { x | ε ≤ dist (f i x) (g x) } ≠ ⊤ := by
    exact fun ε i ↦ (measure_ne_top μ {x | ε ≤ dist (f i x) (g x)})
  constructor
  · intros h ε hε
    have hf : (fun i =>
    (μ { x | ε ≤ dist (f i x) (g x) }).toNNReal) = ENNReal.toNNReal ∘ (fun i =>
    (μ { x | ε ≤ dist (f i x) (g x) })) := by
      exact rfl
    rw [hf, ← ENNReal.tendsto_toNNReal_iff' (hfin ε)]
    exact h ε hε
  · intros h ε hε
    rw [ENNReal.tendsto_toNNReal_iff ENNReal.zero_ne_top (hfin ε) ]
    exact h ε hε

-- Convergence in measure is stable under taking subsequences.
lemma TendstoInMeasure.mono [Dist E] {f : ι → α → E}  {g : α → E} {u v : Filter ι} (huv : v ≤ u)
    (hg :  TendstoInMeasure μ f u g) : TendstoInMeasure μ f v g :=
  fun ε hε => (hg ε hε).mono_left huv

lemma TendstoInMeasure.subseq [Dist E] {f : ℕ → α → E}  {g : α → E} {ns : ℕ → ℕ}
    (hns : StrictMono ns) (hg :  TendstoInMeasure μ f atTop g) :
    TendstoInMeasure μ (f ∘ ns) atTop g := by
  intro ε hε
  apply Filter.Tendsto.comp (hg ε hε) (StrictMono.tendsto_atTop hns)

lemma TendstoInMeasure.subseq' [Dist E] {f : ι → α → E}  {g : α → E} {u : Filter ι}
    {v : Filter κ} {ns : κ → ι} (hns : Tendsto ns v u) (hg :  TendstoInMeasure μ f u g) :
    TendstoInMeasure μ (f ∘ ns) v g := by
  intro ε hε
  apply Filter.Tendsto.comp (hg ε hε) hns

namespace TendstoInMeasure

variable [Dist E] {l : Filter ι} {f f' : ι → α → E} {g g' : α → E}

protected theorem congr' (h_left : ∀ᶠ i in l, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' := by
  intro ε hε
  suffices
    (fun i => μ { x | ε ≤ dist (f' i x) (g' x) }) =ᶠ[l] fun i => μ { x | ε ≤ dist (f i x) (g x) } by
    rw [tendsto_congr' this]
    exact h_tendsto ε hε
  filter_upwards [h_left] with i h_ae_eq
  refine measure_congr ?_
  filter_upwards [h_ae_eq, h_right] with x hxf hxg
  rw [eq_iff_iff]
  change ε ≤ dist (f' i x) (g' x) ↔ ε ≤ dist (f i x) (g x)
  rw [hxg, hxf]

protected theorem congr (h_left : ∀ i, f i =ᵐ[μ] f' i) (h_right : g =ᵐ[μ] g')
    (h_tendsto : TendstoInMeasure μ f l g) : TendstoInMeasure μ f' l g' :=
  TendstoInMeasure.congr' (Eventually.of_forall h_left) h_right h_tendsto

theorem congr_left (h : ∀ i, f i =ᵐ[μ] f' i) (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f' l g :=
  h_tendsto.congr h EventuallyEq.rfl

theorem congr_right (h : g =ᵐ[μ] g') (h_tendsto : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ f l g' :=
  h_tendsto.congr (fun _ => EventuallyEq.rfl) h

end TendstoInMeasure

section ExistsSeqTendstoAe

variable [MetricSpace E]
variable {f : ℕ → α → E} {g : α → E}

/-- Auxiliary lemma for `tendstoInMeasure_of_tendsto_ae`. -/
theorem tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable [IsFiniteMeasure μ]
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  refine fun ε hε => ENNReal.tendsto_atTop_zero.mpr fun δ hδ => ?_
  by_cases hδi : δ = ∞
  · simp only [hδi, imp_true_iff, le_top, exists_const]
  lift δ to ℝ≥0 using hδi
  rw [gt_iff_lt, ENNReal.coe_pos, ← NNReal.coe_pos] at hδ
  obtain ⟨t, _, ht, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto' hf hg hfg hδ
  rw [ENNReal.ofReal_coe_nnreal] at ht
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hunif ε hε)
  refine ⟨N, fun n hn => ?_⟩
  suffices { x : α | ε ≤ dist (f n x) (g x) } ⊆ t from (measure_mono this).trans ht
  rw [← Set.compl_subset_compl]
  intro x hx
  rw [Set.mem_compl_iff, Set.nmem_setOf_iff, dist_comm, not_le]
  exact hN n hn x hx

/-- Convergence a.e. implies convergence in measure in a finite measure space. -/
theorem tendstoInMeasure_of_tendsto_ae [IsFiniteMeasure μ] (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : TendstoInMeasure μ f atTop g := by
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hfg
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_ae_of_stronglyMeasurable
    (fun i => (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have hf_eq_ae : ∀ᵐ x ∂μ, ∀ n, (hf n).mk (f n) x = f n x :=
    ae_all_iff.mpr fun n => (hf n).ae_eq_mk.symm
  filter_upwards [hf_eq_ae, hg.ae_eq_mk, hfg] with x hxf hxg hxfg
  rw [← hxg, funext fun n => hxf n]
  exact hxfg

namespace ExistsSeqTendstoAe

theorem exists_nat_measure_lt_two_inv (hfg : TendstoInMeasure μ f atTop g) (n : ℕ) :
    ∃ N, ∀ m ≥ N, μ { x | (2 : ℝ)⁻¹ ^ n ≤ dist (f m x) (g x) } ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  specialize hfg ((2⁻¹ : ℝ) ^ n) (by simp only [Real.rpow_natCast, inv_pos, zero_lt_two, pow_pos])
  rw [ENNReal.tendsto_atTop_zero] at hfg
  exact hfg ((2 : ℝ≥0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr fun h_zero => by simpa using pow_eq_zero h_zero)

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
    μ { x | (2 : ℝ)⁻¹ ^ n ≤ dist (f k x) (g x) } ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
  cases n
  · exact Classical.choose_spec (exists_nat_measure_lt_two_inv hfg 0) k hn
  · exact Classical.choose_spec
      (exists_nat_measure_lt_two_inv hfg _) _ (le_trans (le_max_left _ _) hn)

theorem seqTendstoAeSeq_strictMono (hfg : TendstoInMeasure μ f atTop g) :
    StrictMono (seqTendstoAeSeq hfg) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [seqTendstoAeSeq_succ]
  exact lt_of_lt_of_le (lt_add_one <| seqTendstoAeSeq hfg n) (le_max_right _ _)

end ExistsSeqTendstoAe

/-- If `f` is a sequence of functions which converges in measure to `g`, then there exists a
subsequence of `f` which converges a.e. to `g`. -/
theorem TendstoInMeasure.exists_seq_tendsto_ae (hfg : TendstoInMeasure μ f atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  /- Since `f` tends to `g` in measure, it has a subsequence `k ↦ f (ns k)` such that
    `μ {|f (ns k) - g| ≥ 2⁻ᵏ} ≤ 2⁻ᵏ` for all `k`. Defining
    `s := ⋂ k, ⋃ i ≥ k, {|f (ns k) - g| ≥ 2⁻ᵏ}`, we see that `μ s = 0` by the
    first Borel-Cantelli lemma.

    On the other hand, as `s` is precisely the set for which `f (ns k)`
    doesn't converge to `g`, `f (ns k)` converges almost everywhere to `g` as required. -/
  have h_lt_ε_real : ∀ (ε : ℝ) (_ : 0 < ε), ∃ k : ℕ, 2 * (2 : ℝ)⁻¹ ^ k < ε := by
    intro ε hε
    obtain ⟨k, h_k⟩ : ∃ k : ℕ, (2 : ℝ)⁻¹ ^ k < ε := exists_pow_lt_of_lt_one hε (by norm_num)
    refine ⟨k + 1, (le_of_eq ?_).trans_lt h_k⟩
    rw [pow_add]; ring
  set ns := ExistsSeqTendstoAe.seqTendstoAeSeq hfg
  use ns
  let S := fun k => { x | (2 : ℝ)⁻¹ ^ k ≤ dist (f (ns k) x) (g x) }
  have hμS_le : ∀ k, μ (S k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    fun k => ExistsSeqTendstoAe.seqTendstoAeSeq_spec hfg k (ns k) le_rfl
  set s := Filter.atTop.limsup S with hs
  have hμs : μ s = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS_le))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.two_ne_top
  have h_tendsto : ∀ x ∈ sᶜ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
    refine fun x hx => Metric.tendsto_atTop.mpr fun ε hε => ?_
    rw [hs, limsup_eq_iInf_iSup_of_nat] at hx
    simp only [S, Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.compl_iInter, Set.compl_iUnion,
      Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
    obtain ⟨N, hNx⟩ := hx
    obtain ⟨k, hk_lt_ε⟩ := h_lt_ε_real ε hε
    refine ⟨max N (k - 1), fun n hn_ge => lt_of_le_of_lt ?_ hk_lt_ε⟩
    specialize hNx n ((le_max_left _ _).trans hn_ge)
    have h_inv_n_le_k : (2 : ℝ)⁻¹ ^ n ≤ 2 * (2 : ℝ)⁻¹ ^ k := by
      rw [mul_comm, ← inv_mul_le_iff₀' (zero_lt_two' ℝ)]
      conv_lhs =>
        congr
        rw [← pow_one (2 : ℝ)⁻¹]
      rw [← pow_add, add_comm]
      exact pow_le_pow_of_le_one (one_div (2 : ℝ) ▸ one_half_pos.le)
        (inv_le_one_of_one_le₀ one_le_two)
        ((le_tsub_add.trans (add_le_add_right (le_max_right _ _) 1)).trans
          (add_le_add_right hn_ge 1))
    exact le_trans hNx.le h_inv_n_le_k
  rw [ae_iff]
  refine ⟨ExistsSeqTendstoAe.seqTendstoAeSeq_strictMono hfg, measure_mono_null (fun x => ?_) hμs⟩
  rw [Set.mem_setOf_eq, ← @Classical.not_not (x ∈ s), not_imp_not]
  exact h_tendsto x

theorem TendstoInMeasure.exists_seq_tendstoInMeasure_atTop {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ (ns : ℕ → ι) (_ : Tendsto ns atTop u),  TendstoInMeasure μ (fun n => f (ns n)) atTop g := by
  obtain ⟨ns, h_tendsto_ns⟩ : ∃ ns : ℕ → ι, Tendsto ns atTop u := exists_seq_tendsto u
  exact ⟨ns, h_tendsto_ns, fun ε hε => (hfg ε hε).comp h_tendsto_ns⟩

theorem TendstoInMeasure.exists_seq_tendsto_ae' {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hfg : TendstoInMeasure μ f u g) :
    ∃ (ns : ℕ → ι) (_ : Tendsto ns atTop u),
    ∀ᵐ x ∂μ, Tendsto (fun i => f (ns i) x) atTop (𝓝 (g x)) := by
  obtain ⟨ms, hms1, hms2⟩ := hfg.exists_seq_tendstoInMeasure_atTop
  obtain ⟨ns, hns1, hns2⟩ := hms2.exists_seq_tendsto_ae
  exact ⟨ms ∘ ns, Tendsto.comp hms1 (StrictMono.tendsto_atTop hns1), hns2⟩

section

/- An auxiliary lemma for a proof by contradiction in exists_seq_tendstoInMeasure_atTop_iff -/
lemma false_of_tendsto_of_bddBelow_aux (f : ℕ → ℝ≥0) (δ : ℝ) (hδ: (0 : ℝ) < δ)
    (hf1 : Tendsto f atTop (𝓝 0)) (hf2 : ∀ n, δ ≤ (f n) ) : False := by
  have h : ∀ x : ℝ≥0, x.toReal = dist x 0 := by
    intro x
    rw [NNReal.dist_eq x 0, NNReal.coe_zero, sub_zero, NNReal.abs_eq]
  simp_rw [h] at hf2
  apply Metric.false_of_Tendsto_of_bddBelow
    hδ (Tendsto.comp (NNReal.tendsto_coe'.mpr ⟨Preorder.le_refl 0, fun ⦃_⦄ a ↦ a ⟩) hf1) _
  refine frequently_atTop'.mpr ?_
  intro n
  use n+1
  simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, Function.comp_apply, dist_zero_right,
    Real.norm_eq_abs, NNReal.abs_eq, true_and]
  have h : ∀ n, dist (f n) 0 = f n := by
    exact fun n ↦ Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (h (f n))))
  rw [← h]
  exact hf2 (n+1)

end

lemma forall_seq_tendstoInMeasure_atTop {u : Filter ι} {v : Filter κ} {f : ι → α → E}
    {g : α → E} {ns : κ → ι} (hfg : TendstoInMeasure μ f u g) (hns : Tendsto ns v u) :
    TendstoInMeasure μ (fun n => f (ns n)) v g :=
  fun ε hε => (hfg ε hε).comp hns

lemma subseq_of_not_tendsto {f : ℕ → NNReal} (h : ¬Tendsto f atTop (𝓝 (0 : ℝ≥0))) :
    ∃ ε > 0, ∃ (ns : ℕ → ℕ) (_ : StrictMono ns), ∀ n, ε ≤ (f (ns n)).toReal := by
  rw [Filter.not_tendsto_iff_exists_frequently_nmem] at h
  rcases h with ⟨A, ⟨hA1, hA2⟩⟩
  rw [Metric.mem_nhds_iff] at hA1
  rcases (Filter.extraction_of_frequently_atTop hA2) with ⟨ns, hns, h4⟩
  rcases hA1 with ⟨ε, hε, h3⟩
  use ε, hε, ns, hns
  intro n
  rw [← NNReal.abs_eq, ← Real.norm_eq_abs, ← not_lt, ← mem_ball_zero_iff]
  exact fun a => (h4 n) (h3 a)

/- TendstoInMeasure is equivalent to a proof  that every subsequence has another subsequence
which converges almost surely. -/
theorem exists_seq_tendstoInMeasure_atTop_iff (hfin : MeasureTheory.IsFiniteMeasure μ)
    {f : ℕ → α → E} (hf : ∀ (n : ℕ), AEStronglyMeasurable (f n) μ) {g : α → E} :
    (TendstoInMeasure μ f atTop g) ↔
    ∀ (ns : ℕ → ℕ) (_ : StrictMono ns), ∃ (ns' : ℕ → ℕ) (_ : StrictMono ns'), ∀ᵐ (ω : α) ∂μ,
    Tendsto (fun i ↦ f (ns (ns' i)) ω) atTop (𝓝 (g ω)) := by
  rw [tendstoInMeasure_iff_tendsto_toNNReal]
  constructor
  · intros hfg ns hns
    have h1 : TendstoInMeasure μ (f ∘ ns)
      atTop g := (TendstoInMeasure.subseq hns
      (tendstoInMeasure_iff_tendsto_toNNReal.mpr hfg))
    have ⟨ns', hns1, hns2⟩ :=
    TendstoInMeasure.exists_seq_tendsto_ae h1
    use ns', hns1
    filter_upwards [hns2] with x hns3
    exact hns3
  · rw [← not_imp_not]
    intros h1
    push_neg
    obtain h2 : ∃ (ε : ℝ) (_ : 0 < ε),
      ¬(Tendsto (fun n => (μ { x | ε ≤ dist (f n x) (g x) }).toNNReal) atTop (𝓝 0)) := by
      · by_contra h3
        apply h1
        push_neg at h3
        exact h3
    rcases h2 with ⟨ε, hε, h4⟩
    obtain h5 := @subseq_of_not_tendsto (fun n ↦ (μ {x | ε ≤ dist (f n x) (g x)}).toNNReal) h4
    rcases h5 with ⟨δ, hδ, ns, hns, h5⟩
    use ns, hns
    intros ns' _
    by_contra h6
    apply h4
    have h4 : ∀ (n : ℕ), AEStronglyMeasurable ((f ∘ ns ∘ ns') n) μ := by exact fun n ↦
      (hf ((ns ∘ ns') n))
    have h8 := (MeasureTheory.tendstoInMeasure_of_tendsto_ae (f := f ∘ ns ∘ ns') (h4) h6)
    obtain h7 := fun n => h5 (ns' n)
    rw [tendstoInMeasure_iff_tendsto_toNNReal] at h8
    exfalso
    revert h7
    apply false_of_tendsto_of_bddBelow_aux
      (fun n => (μ {x | ε ≤ dist (f (ns (ns' n)) x) (g x)}).toNNReal) δ hδ (h8 ε hε)

section

end

end ExistsSeqTendstoAe

section LimitInMeasureUnique

variable [MetricSpace E]
variable {f : ℕ → α → E} {g h : α → E}

-- The LimitInMeasure is ae unique
theorem ae_unique_of_limitInMeasure' (hg : TendstoInMeasure μ f atTop g)
    (hh : TendstoInMeasure μ f atTop h) : g =ᵐ[μ] h := by
  obtain ⟨ns,h1,h1'⟩ := TendstoInMeasure.exists_seq_tendsto_ae hg
  obtain ⟨ns', h2, h2'⟩ :=
    TendstoInMeasure.exists_seq_tendsto_ae (TendstoInMeasure.subseq h1 hh)
  obtain h4 : ∀ᵐ (x : α) ∂μ, Tendsto (fun i ↦ f (ns (ns' i)) x) atTop (𝓝 (g x)) := by
    filter_upwards [h1'] with ω h
    apply Filter.Tendsto.comp h (StrictMono.tendsto_atTop h2)
  filter_upwards [h4, h2'] with ω hg1 hh1
  refine tendsto_nhds_unique hg1 hh1

-- Same as above but with a more general filter on ι
theorem ae_unique_of_limitInMeasure {g h : α → E} {f : ι → α → E}  {u : Filter ι} [NeBot u]
    [IsCountablyGenerated u] (hg : TendstoInMeasure μ f u g) (hh : TendstoInMeasure μ f u h) :
    g =ᵐ[μ] h := by
  obtain ⟨ns,h1,h1'⟩ := TendstoInMeasure.exists_seq_tendstoInMeasure_atTop hg
  exact ae_unique_of_limitInMeasure' (f := f ∘ ns) h1' (TendstoInMeasure.subseq' h1 hh)

end LimitInMeasureUnique

section AEMeasurableOf

variable [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]

theorem TendstoInMeasure.aemeasurable {u : Filter ι} [NeBot u] [IsCountablyGenerated u]
    {f : ι → α → E} {g : α → E} (hf : ∀ n, AEMeasurable (f n) μ)
    (h_tendsto : TendstoInMeasure μ f u g) : AEMeasurable g μ := by
  obtain ⟨ns, -, hns⟩ := h_tendsto.exists_seq_tendsto_ae'
  exact aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hf (ns n)) hns

end AEMeasurableOf

section TendstoInMeasureOf

variable [NormedAddCommGroup E] {p : ℝ≥0∞}
variable {f : ι → α → E} {g : α → E}

/-- This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` where we
allow `p = ∞` and only require `AEStronglyMeasurable`. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro ε hε
  replace hfg := ENNReal.Tendsto.const_mul
    (Tendsto.ennrpow_const p.toReal hfg) (Or.inr <| @ENNReal.ofReal_ne_top (1 / ε ^ p.toReal))
  simp only [mul_zero,
    ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp_ne_zero hp_ne_top)] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro δ hδ
  refine (hfg δ hδ).mono fun n hn => ?_
  refine le_trans ?_ hn
  rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hε _), ENNReal.ofReal_one, mul_comm,
    mul_one_div, ENNReal.le_div_iff_mul_le _ (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  · rw [← ENNReal.ofReal_rpow_of_pos hε]
    convert mul_meas_ge_le_pow_eLpNorm' μ hp_ne_zero hp_ne_top ((hf n).sub hg).aestronglyMeasurable
        (ENNReal.ofReal ε)
    rw [dist_eq_norm, ← ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), ofReal_norm_eq_coe_nnnorm]
    exact Iff.rfl
  · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Or.inl (Real.rpow_pos_of_pos hε _)

@[deprecated (since := "2024-07-27")]
alias tendstoInMeasure_of_tendsto_snorm_of_stronglyMeasurable :=
  tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable

/-- This lemma is superseded by `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` where we
allow `p = ∞`. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ) {l : Filter ι}
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  refine TendstoInMeasure.congr (fun i => (hf i).ae_eq_mk.symm) hg.ae_eq_mk.symm ?_
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_stronglyMeasurable
    hp_ne_zero hp_ne_top (fun i => (hf i).stronglyMeasurable_mk) hg.stronglyMeasurable_mk ?_
  have : (fun n => eLpNorm ((hf n).mk (f n) - hg.mk g) p μ) = fun n => eLpNorm (f n - g) p μ := by
    ext1 n; refine eLpNorm_congr_ae (EventuallyEq.sub (hf n).ae_eq_mk.symm hg.ae_eq_mk.symm)
  rw [this]
  exact hfg

@[deprecated (since := "2024-07-27")]
alias tendstoInMeasure_of_tendsto_snorm_of_ne_top := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top

/-- See also `MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm` which work for general
Lp-convergence for all `p ≠ 0`. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm_top {E} [NormedAddCommGroup E] {f : ι → α → E}
    {g : α → E} {l : Filter ι} (hfg : Tendsto (fun n => eLpNorm (f n - g) ∞ μ) l (𝓝 0)) :
    TendstoInMeasure μ f l g := by
  intro δ hδ
  simp only [eLpNorm_exponent_top, eLpNormEssSup] at hfg
  rw [ENNReal.tendsto_nhds_zero] at hfg ⊢
  intro ε hε
  specialize hfg (ENNReal.ofReal δ / 2)
      (ENNReal.div_pos_iff.2 ⟨(ENNReal.ofReal_pos.2 hδ).ne.symm, ENNReal.two_ne_top⟩)
  refine hfg.mono fun n hn => ?_
  simp only [gt_iff_lt, zero_tsub, zero_le, zero_add, Set.mem_Icc,
    Pi.sub_apply] at *
  have : essSup (fun x : α => (‖f n x - g x‖₊ : ℝ≥0∞)) μ < ENNReal.ofReal δ :=
    lt_of_le_of_lt hn
      (ENNReal.half_lt_self (ENNReal.ofReal_pos.2 hδ).ne.symm ENNReal.ofReal_lt_top.ne)
  refine ((le_of_eq ?_).trans (ae_lt_of_essSup_lt this).le).trans hε.le
  congr with x
  simp only [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_lt_top.ne, ENNReal.coe_toReal, not_lt,
    coe_nnnorm, Set.mem_setOf_eq, Set.mem_compl_iff]
  rw [← dist_eq_norm (f n x) (g x)]

@[deprecated (since := "2024-07-27")]
alias tendstoInMeasure_of_tendsto_snorm_top := tendstoInMeasure_of_tendsto_eLpNorm_top

/-- Convergence in Lp implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_eLpNorm {l : Filter ι} (hp_ne_zero : p ≠ 0)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hfg : Tendsto (fun n => eLpNorm (f n - g) p μ) l (𝓝 0)) : TendstoInMeasure μ f l g := by
  by_cases hp_ne_top : p = ∞
  · subst hp_ne_top
    exact tendstoInMeasure_of_tendsto_eLpNorm_top hfg
  · exact tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top hp_ne_zero hp_ne_top hf hg hfg

@[deprecated (since := "2024-07-27")]
alias tendstoInMeasure_of_tendsto_snorm := tendstoInMeasure_of_tendsto_eLpNorm

/-- Convergence in Lp implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_Lp [hp : Fact (1 ≤ p)] {f : ι → Lp E p μ} {g : Lp E p μ}
    {l : Filter ι} (hfg : Tendsto f l (𝓝 g)) : TendstoInMeasure μ (fun n => f n) l g :=
  tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hp.elim).ne.symm
    (fun _ => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    ((Lp.tendsto_Lp_iff_tendsto_ℒp' _ _).mp hfg)

end TendstoInMeasureOf

end MeasureTheory
