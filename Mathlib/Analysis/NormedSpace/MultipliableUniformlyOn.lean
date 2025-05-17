/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Uniform convergence of products of functions

We gather some results about the uniform convergence of infinite products, in particular those of
the form `∏' i, (1 + f i x)` for a sequence `f` of functions.
-/

open Filter Function Complex Finset Topology

variable {α β ι : Type*} [UniformSpace β] [AddGroup β] [IsUniformAddGroup β] [LinearOrder β]
  [OrderTopology β] [AddLeftMono β] [AddRightMono β]
section cexp_clog

lemma TendstoUniformlyOn.eventually_forall_lt {f : ι → α → β} {p : Filter ι} {g : α → β}
    {K : Set α} {u v : β} (huv : u < v) (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x < v := by
  simp only [tendstoUniformlyOn_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
    tendsto_iff_eventually, eventually_comap, Prod.forall] at *
  conv at hf => enter [2]; rw [eventually_iff_exists_mem]
  have hf2 := hf (fun x ↦ -x.1 + x.2 < -u + v) ⟨_, (isOpen_gt' (-u + v)).mem_nhds (by simp [huv]),
    fun y hy a b hab => (hab.symm ▸ hy :)⟩
  rw [eventually_prod_principal_iff] at *
  filter_upwards [hf2] with i hi x hx
  simpa using add_lt_add_of_le_of_lt (hg x hx) (hi x hx)

lemma TendstoUniformlyOn.eventually_forall_le {f : ι → α → β} {p : Filter ι} {g : α → β}
    {K : Set α} {u v : β} (huv : u < v) (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x ≤ v := by
  filter_upwards [hf.eventually_forall_lt huv hg] with i hi x hx using (hi x hx).le

lemma TendstoUniformlyOn.comp_cexp {p : Filter ι} {f : ι → α → ℂ} {g : α → ℂ}
    {K : Set α} (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x ↦ (g x).re) '' K) :
    TendstoUniformlyOn (cexp ∘ f ·) (cexp ∘ g) p K := by
  obtain ⟨v, hv⟩ : ∃ v, ∀ x ∈ K, (g x).re ≤ v := hg.imp fun _ h ↦ by simpa [mem_upperBounds] using h
  have : ∀ᶠ i in p, ∀ x ∈ K, (f i x).re ≤ v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  simpa using fun a ha ↦ (hv a ha).trans (lt_add_one v).le

lemma Complex.tendstoUniformlyOn_tsum_log_one_add {α : Type*} {f : ι → α → ℂ} (K : Set α)
    {u : ι → ℝ} (hu : Summable u) (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun s a ↦ ∑ i ∈ s, log (1 + f i a)) (fun a ↦ ∑' i, log (1 + f i a))
    atTop K := by
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually <| hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hn' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hn').trans (by simpa using hi x hx)

lemma Complex.HasSumUniformlyOn_log_one_add {α : Type*} {f : ι → α → ℂ} (K : Set α)
    {u : ι → ℝ} (hu : Summable u) (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn (fun i a ↦ log (1 + f i a)) (fun a ↦ ∑' i, log (1 + f i a)) {K} := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    Complex.tendstoUniformlyOn_tsum_log_one_add K hu h]

lemma Complex.tendstoUniformlyOn_tsum_nat_log_one_add {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun n a => ∑ i ∈ Finset.range n,
    (Complex.log (1 + f i a))) (fun a => ∑' i : ℕ, Complex.log (1 + f i a)) atTop K := by
  apply tendstoUniformlyOn_tsum_nat_eventually (hu.mul_left (3/2))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero hu) (1/2) (one_half_pos)
  simp only [eventually_atTop, ge_iff_le] at *
  obtain ⟨N2, hN2⟩ := h
  refine ⟨max N N2, fun n hn x hx => ?_⟩
  apply le_trans (Complex.norm_log_one_add_half_le_self (z := (f n x)) ?_)
  · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_left]
    exact hN2 n (le_of_max_le_right hn) x hx
  · apply le_trans (le_trans (hN2 n (le_of_max_le_right hn) x hx)
    (by simpa using Real.le_norm_self (u n))) (hN n (le_of_max_le_left hn)).le

end cexp_clog

section UniformlyOn

lemma HasProdUniformlyOn_of_clog {f : ι → α → ℂ} {K : Set α}
    (hf : SummableUniformlyOn (fun i a => log (f i a)) {K}) (hfn : ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : BddAbove <| (fun x => (∑' n : ι, log (f n x)).re) '' K) :
    HasProdUniformlyOn f (fun a => ∏' i, f i a) {K} := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq]
  obtain ⟨r, hr⟩ := hf.exists
  suffices H : TendstoUniformlyOn (fun s a => ∏ i ∈ s, f i a) (cexp ∘ r) atTop K by
        apply TendstoUniformlyOn.congr_right H
        apply Set.EqOn.trans (Set.EqOn.comp_left (hr.tsum_eqOn (by simp))).symm
        exact fun x hx ↦ (cexp_tsum_eq_tprod (hfn x hx) (hf.summable (by simp) hx))
  have h1 := (hr.tsum_eqOn (s := K) (by simp))
  rw [hasSumUniformlyOn_iff_tendstoUniformlyOn] at hr
  simp only [Set.mem_singleton_iff, forall_eq] at hr
  apply TendstoUniformlyOn.congr (hr.comp_cexp ?_)
  · filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn i hi y)]
  · convert hg
    next a ha => simp_all only [h1 ha, ne_eq]

lemma HasProdUniformlyOn_nat_one_add [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hfn : ∀ x ∈ K, ∀ n, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdUniformlyOn (fun n a => (1 + f n a)) (fun a => ∏' i, (1 + f i a)) {K} := by
  refine HasProdUniformlyOn_of_clog ?_ hfn (hK.bddAbove_image ?_)
  · apply HasSumUniformlyOn.summableUniformlyOn (g := fun x => ∑' i, log (1 + f i x))
    apply Complex.HasSumUniformlyOn_log_one_add K hu (Nat.cofinite_eq_atTop ▸ h)
  · apply (tendstoUniformlyOn_tsum_nat_log_one_add K hu h).re.continuousOn
    filter_upwards with n
    simp only [re_sum, log_re]
    refine continuousOn_finset_sum _ fun c _ ↦ ?_
    exact (continuousOn_const.add (hcts c)).norm.log (fun z hz ↦ by simpa using hfn z hz c)

lemma MultipliableUniformlyOn_nat_one_add [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hfn : ∀ x ∈ K, ∀ n, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableUniformlyOn (fun n a => (1 + f n a)) {K} :=
  ⟨(fun a => ∏' i, (1 + f i a)), HasProdUniformlyOn_nat_one_add hK hu h hfn hcts⟩

lemma HasProdLocallyUniformlyOn_nat_one_add [TopologicalSpace α] [LocallyCompactSpace α]
    {f : ℕ → α → ℂ} {K : Set α} (hK : IsOpen K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hfn : ∀ x ∈ K, ∀ n, 1 + f n x ≠ 0)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdLocallyUniformlyOn (fun n a => (1 + f n a)) (fun a => ∏' i, (1 + (f i a))) K := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  intro S hS hS2
  apply HasProdUniformlyOn_nat_one_add hS2 hu ?_ (by tauto) fun n => (hcts n).mono hS
  filter_upwards [h] with n hn a ha using hn a (hS ha)

lemma MultipliableLocallyUniformlyOn_nat_one_add [TopologicalSpace α] [LocallyCompactSpace α]
    {f : ℕ → α → ℂ} {K : Set α} (hK : IsOpen K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hfn : ∀ x ∈ K, ∀ n, 1 + f n x ≠ 0)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableLocallyUniformlyOn (fun n a => (1 + f n a)) K :=
  ⟨(fun a => ∏' i, (1 + (f i a))), HasProdLocallyUniformlyOn_nat_one_add hK hu h hfn hcts⟩

end UniformlyOn
