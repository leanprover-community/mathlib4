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

lemma Complex.HasSumUniformlyOn_log_one_add {α : Type*} {f : ι → α → ℂ} (K : Set α)
    {u : ι → ℝ} (hu : Summable u) (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn (fun i a ↦ log (1 + f i a)) (fun a ↦ ∑' i, log (1 + f i a)) {K} := by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually <| hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hn' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hn').trans (by simpa using hi x hx)

lemma Complex.tendstoUniformlyOn_tsum_nat_log_one_add {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun n a => ∑ i ∈ Finset.range n,
    (Complex.log (1 + f i a))) (fun a => ∑' i : ℕ, Complex.log (1 + f i a)) atTop K := by
  rw [← Nat.cofinite_eq_atTop ] at h
  simpa only [Set.mem_singleton_iff, forall_eq] using
    hasSumUniformlyOn_tendstoUniformlyOn_nat (Complex.HasSumUniformlyOn_log_one_add K hu h)

end cexp_clog

section UniformlyOn

lemma HasProdUniformlyOn_of_clog {f : ι → α → ℂ} {𝔖 : Set (Set α)}
    (hf : SummableUniformlyOn (fun i a => log (f i a)) 𝔖) (hfn : ∀ K ∈ 𝔖, ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : ∀ K ∈ 𝔖, BddAbove <| (fun x => (∑' n : ι, log (f n x)).re) '' K) :
    HasProdUniformlyOn f (fun a => ∏' i, f i a) 𝔖 := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq]
  obtain ⟨r, hr⟩ := hf.exists
  intro K hK
  suffices H : TendstoUniformlyOn (fun s a => ∏ i ∈ s, f i a) (cexp ∘ r) atTop K by
        apply TendstoUniformlyOn.congr_right H
        apply Set.EqOn.trans (Set.EqOn.comp_left (hr.tsum_eqOn hK)).symm
        exact fun x hx ↦ (cexp_tsum_eq_tprod (hfn K hK x hx) (hf.summable hK hx))
  have h1 := (hr.tsum_eqOn (s := K) hK)
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq] at hr
  apply TendstoUniformlyOn.congr ((hr K hK).comp_cexp ?_)
  · filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn K hK i hi y)]
  · convert hg K hK
    next a ha => simp_all only [h1 ha, ne_eq]

lemma HasProdUniformlyOn_nat_one_add [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hfn : ∀ x ∈ K, ∀ n, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdUniformlyOn (fun n a => (1 + f n a)) (fun a => ∏' i, (1 + f i a)) {K} := by
  refine HasProdUniformlyOn_of_clog ?_ (by simpa using hfn) ?_
  · apply HasSumUniformlyOn.summableUniformlyOn (g := fun x => ∑' i, log (1 + f i x))
    apply Complex.HasSumUniformlyOn_log_one_add K hu (Nat.cofinite_eq_atTop ▸ h)
  · simp only [Set.mem_singleton_iff, forall_eq]
    apply (hK.bddAbove_image)
    apply (tendstoUniformlyOn_tsum_nat_log_one_add K hu h).re.continuousOn
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
