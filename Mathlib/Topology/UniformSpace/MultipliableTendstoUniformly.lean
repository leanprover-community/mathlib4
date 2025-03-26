/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Uniform convergence of products of functions

We gather some results about the uniform convergence of infinite products, in particular those of
the form `∏' i, (1 + f i x)` for a sequence `f` of functions.
-/

open Filter Function Complex

variable {α β ι : Type*} [UniformSpace β] [AddGroup β]
    [UniformAddGroup β] [LinearOrder β] [OrderTopology β] [AddLeftMono β] [AddRightMono β]

lemma TendstoUniformlyOn.eventually_forall_lt {f : ι → α → β} {p : Filter ι} {g : α → β}
    {K : Set α} {u v : β} (huv : u < v)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x < v := by
  rw [tendstoUniformlyOn_iff_tendsto] at hf
  simp only [uniformity_eq_comap_neg_add_nhds_zero, tendsto_iff_eventually, eventually_comap,
    Prod.forall] at *
  conv at hf => enter [2]; rw [eventually_iff_exists_mem]
  have hf2 := hf (fun x ↦ -x.1 + x.2 < -u + v) ⟨_, (isOpen_gt' (-u + v)).mem_nhds (by simp [huv]),
    fun y hy a b hab => (hab.symm ▸ hy :)⟩
  rw [eventually_prod_principal_iff, eventually_iff_exists_mem] at *
  obtain ⟨t, ht, H⟩ := hf2
  refine ⟨t, ht, fun y hy x hx => by simpa using (add_lt_add_of_le_of_lt (hg x hx) (H y hy x hx))⟩

lemma TendstoUniformlyOn.eventually_forall_le {f : ι → α → β} {p : Filter ι} {g : α → β}
    {K : Set α} {u v : β} (huv : u < v) (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x ≤ v := by
    filter_upwards [hf.eventually_forall_lt huv hg] with i hi x hx using (hi x hx).le

lemma tendstoUniformlyOn_comp_cexp {p : Filter ι} {f : ι → α → ℂ} {g : α → ℂ}
    {K : Set α} (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x ↦ (g x).re) '' K) :
    TendstoUniformlyOn (cexp ∘ f ·) (cexp ∘ g) p K := by
  obtain ⟨v, hv⟩ : ∃ v, ∀ x ∈ K, (g x).re ≤ v := hg.imp fun _ h ↦ by simpa [mem_upperBounds] using h
  have : ∀ᶠ i in p, ∀ x ∈ K, (f i x).re ≤ v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  rw [tendstouniformlyOn_iff_restrict]
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformly_eventually _ _ _ (by simpa) ?_
    (tendstouniformlyOn_iff_restrict.mp hf)
  simpa using fun a ha ↦ (hv a ha).trans (lt_add_one v).le

lemma tendstoUniformlyOn_tprod_of_clog {f : ι → α → ℂ} {K : Set α}
    (h : ∀ x ∈ K, Summable fun i => log (f i x))
    (hf : TendstoUniformlyOn (fun s a => ∑ i ∈ s, log (f i a))
    (fun a => ∑' i, log (f i a)) atTop K) (hfn : ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : BddAbove ((fun x => (∑' n : ι, log (f n x)).re) '' K)) :
    TendstoUniformlyOn (fun s a => ∏ i ∈ s, f i a) (fun a => ∏' i, f i a) atTop K := by
  suffices H : TendstoUniformlyOn (fun s a => ∏ i ∈ s, f i a)
       (cexp ∘ fun a ↦ ∑' i, log (f i a)) atTop K by
        apply TendstoUniformlyOn.congr_right H
        exact fun x hx ↦ (cexp_tsum_eq_tprod (fun n ↦ f n x) (hfn x hx) (h x hx))
  apply TendstoUniformlyOn.congr (tendstoUniformlyOn_comp_cexp hf hg)
  filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn i hi y)]

/-- This is the version of `tendstoUniformlyOn_tprod_of_clog`
for infinite products of with terms of the form `1 + f n x`. -/
lemma tendstoUniformlyOn_tprod_nat_one_add [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hfn : ∀ x ∈ K, ∀ n, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => f n x) K) :
    TendstoUniformlyOn (fun n a => ∏ i ∈ Finset.range n, (1 + f i a))
    (fun a => ∏' i, (1 + f i a)) atTop K := by
  refine fun v hv => tendsto_finset_range.eventually
    (tendstoUniformlyOn_tprod_of_clog ?_ ?_ hfn (hK.bddAbove_image ?_) v hv)
  · intro x hx
    apply Complex.summable_log_one_add_of_summable (Summable.of_norm_bounded_eventually _ hu ?_)
    filter_upwards [Nat.cofinite_eq_atTop ▸ h] with n hn using (hn x hx)
  · exact tendstoUniformlyOn_tsum_log_one_add K hu (Nat.cofinite_eq_atTop ▸ h)
  · apply (tendstoUniformlyOn_tsum_nat_log_one_add K hu h).re.continuousOn
    filter_upwards with n
    simp only [re_sum, log_re]
    refine continuousOn_finset_sum _ fun c _ ↦ ?_
    exact (continuousOn_const.add (hcts c)).norm.log (fun z hz ↦ by simpa using hfn z hz c)

/-- This is the locally version of `tendstoUniformlyOn_tprod_nat_one_add`
for infinite products of with terms of the form `1 + f n x`. -/
lemma tendstoLocallyUniformlyOn_tprod_nat_one_add [TopologicalSpace α] [ LocallyCompactSpace α]
    {f : ℕ → α → ℂ} {K : Set α} (hK : IsOpen K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hfn : ∀ x, x ∈ K → ∀ n, 1 + f n x ≠ 0)
    (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoLocallyUniformlyOn (fun n a => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hK]
  intro S hS hS2
  apply tendstoUniformlyOn_tprod_nat_one_add hS2 hu ?_ (by tauto) fun n => (hcts n).mono hS
  filter_upwards [h] with n hn a ha using hn a (hS ha)
