/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Uniform limits of products of functions

We gather some results about the uniform convergence of the products, in particular those of the
form `1 + f n x` for a sequence `f n x` of complex numbers.

-/

open Filter Function Complex

variable {α β ι : Type*}

lemma TendstoUniformlyOn.eventually_forall_lt [UniformSpace β] [AddGroup β]
    [UniformAddGroup β] [LinearOrder β] [OrderTopology β] [AddLeftStrictMono β] [AddRightMono β]
    {f : ι → α → β} {p : Filter ι} {g : α → β} {K : Set α} {T V : β} (htv : T < V)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x, x ∈ K → g x ≤ T) :
    ∀ᶠ (n : ι) in p, ∀ x, x ∈ K → f n x < V := by
  rw [tendstoUniformlyOn_iff_tendsto] at hf
  simp only [uniformity_eq_comap_neg_add_nhds_zero, tendsto_iff_eventually, eventually_comap,
    Prod.forall] at *
  conv at hf => enter [2]; rw [eventually_iff_exists_mem]
  have hf2 := hf (fun x : β × β => -x.1 + x.2 < -T + V) ⟨{x : β | x < -T + V},
      IsOpen.mem_nhds (isOpen_gt' (-T + V)) (by simp [htv]),
      fun y hy a b hab => by simpa [hab] using hy⟩
  rw [eventually_prod_principal_iff, eventually_iff_exists_mem] at *
  obtain ⟨v, hv, H⟩ := hf2
  refine ⟨v, hv, fun y hy x hx => by simpa using (add_lt_add_of_le_of_lt (hg x hx) (H y hy x hx))⟩

lemma TendstoUniformlyOn.eventually_forall_le [UniformSpace β] [AddGroup β]
    [UniformAddGroup β] [LinearOrder β] [OrderTopology β] [AddLeftStrictMono β] [AddRightMono β]
    (f : ι → α → β)  {p : Filter ι} {g : α → β} {K : Set α} {T V : β} (htv : T < V)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x, x ∈ K → g x ≤ T) :
    ∀ᶠ (n : ι) in p, ∀ x, x ∈ K → f n x ≤ V := by
    filter_upwards [hf.eventually_forall_lt htv hg] with i hi x hx using (hi x hx).le

lemma tendstoUniformlyOn_comp_cexp {p : Filter ι} {f : ι → α → ℂ} {g : α → ℂ}
    {K : Set α} (hf : TendstoUniformlyOn f g p K) (hg : BddAbove ((fun x => (g x).re) '' K)) :
    TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) p K := by
  obtain ⟨T, hT⟩ := hg
  simp only [mem_upperBounds, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hT
  have h2 := TendstoUniformlyOn.eventually_forall_le (fun n x => (f n x).re) (lt_add_one T)
    hf.re hT
  have w2 := tendstoUniformlyOn_univ.mpr <| UniformContinuousOn.comp_tendstoUniformly_eventually
    {x : ℂ | x.re ≤ T + 1} (fun a => K.restrict (f (a))) (fun b => g b) (by simpa using h2) ?_
      (UniformContinuousOn.cexp (T + 1)) ((tendstouniformlyOn_iff_restrict).mp hf)
  · rw [tendstouniformlyOn_iff_restrict, ← tendstoUniformlyOn_univ]
    exact w2
  · simp only [Set.mem_setOf_eq, Subtype.forall]
    exact fun a ha => le_trans (hT a ha) (by aesop)

lemma tendstoUniformlyOn_tprod_of_clog {f : ι → α → ℂ} {K : Set α}
    (h : ∀ x, x ∈ K → Summable fun n => log (f n x))
    (hf : TendstoUniformlyOn (fun n a => ∑ i ∈ n, log (f i a))
    (fun a : α => ∑' n : ι, log (f n a)) atTop K) (hfn : ∀ x, x ∈ K → ∀ n : ι, f n x ≠ 0)
    (hg : BddAbove ((fun x => (∑' n : ι, log (f n x)).re) '' K)) :
    TendstoUniformlyOn (fun n a => ∏ i ∈ n, (f i a)) (fun a => ∏' i, (f i a)) atTop K := by
  suffices HU : TendstoUniformlyOn (fun n a => ∏ i ∈ n, (f i a))
       (cexp ∘ fun a ↦ ∑' n : ι, log (f n a)) atTop K by
        apply TendstoUniformlyOn.congr_right HU
        intro x hx
        simpa using (Complex.cexp_tsum_eq_tprod _ (hfn x hx) (h x hx))
  apply TendstoUniformlyOn.congr (tendstoUniformlyOn_comp_cexp hf hg)
  filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn i hi y)]

/-- This is a version of `tendstoUniformlyOn_tprod_of_clog` for nat that uses range
in the products. -/
lemma tendstoUniformlyOn_tprod_nat_of_clog {f : ℕ → α → ℂ} {K : Set α}
    (h : ∀ x, x ∈ K → Summable fun n => log (f n x))
    (hf : TendstoUniformlyOn (fun n a => ∑ i ∈ n, log (f i a)) (fun a : α => ∑' n : ℕ, log (f n a))
    atTop K) (hfn : ∀ x, x ∈ K → ∀ n : ℕ, f n x ≠ 0)
    (hg : BddAbove ((fun x => (∑' n : ℕ, log (f n x)).re) '' K)) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (f i a))
    (fun a => ∏' i, (f i a)) atTop K :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tprod_of_clog h hf hfn hg v hv)

/-- This is the version for infinite products of with terms of the form `1 + f n x`. -/
lemma tendstoUniformlyOn_tprod_nat [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hfn : ∀ x, x ∈ K → ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => f n x) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + f i a))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  apply tendstoUniformlyOn_tprod_nat_of_clog ?_ ?_ hfn
  · have H : ContinuousOn (fun x ↦ (∑' (n : ℕ), Complex.log (1 + f n x)).re) K := by
      apply (tendstoUniformlyOn_tsum_nat_log_one_add K hu
        (Filter.Eventually.of_forall h)).re.continuousOn
      filter_upwards with n
      simp only [re_sum, log_re]
      apply continuousOn_finset_sum
      intro c _
      apply ContinuousOn.log
      · apply ContinuousOn.comp continuous_norm.continuousOn
          (ContinuousOn.add continuousOn_const (hcts c)) (Set.mapsTo_image (fun x ↦ 1 + f c x) K)
      · intro z hz
        simpa using hfn z hz c
    exact IsCompact.bddAbove_image hK H
  · intro x hx
    exact Complex.summable_log_one_add_of_summable (summable_norm_iff.mp
      (Summable.of_nonneg_of_le (fun b ↦ norm_nonneg (f b ↑x)) (fun _ => h _ _ hx) hu))
  · exact Complex.tendstoUniformlyOn_tsum_log_one_add K hu (Filter.Eventually.of_forall h)

/-- This is the locally version for infinite products of with terms of the form `1 + f n x`. -/
lemma tendstoLocallyUniformlyOn_tprod_nat' [TopologicalSpace α] [ LocallyCompactSpace α]
    {f : ℕ → α → ℂ} {K : Set α} (hK : IsOpen K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)(hfn : ∀ x, x ∈ K → ∀ n : ℕ, 1 + f n x ≠ 0)
    (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoLocallyUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hK]
  intro S hS hS2
  apply tendstoUniformlyOn_tprod_nat hS2 hu
  · exact fun n x hx ↦ h n x (hS hx)
  · exact fun x hx n => hfn x (hS hx) n
  · exact fun n => (hcts n).mono hS
