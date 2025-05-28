/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# Uniform convergence of products of functions

We gather some results about the uniform convergence of infinite products, in particular those of
the form `∏' i, (1 + f i x)` for a sequence `f` of complex valued functions.
-/

open Filter Function Complex Finset Topology

variable {α ι : Type*}

section summable

variable {f : ι → α → ℂ} {g : α → ℂ} {K : Set α} {p : Filter ι}

lemma TendstoUniformlyOn.comp_cexp {f : ι → α → ℂ} {g : α → ℂ}
    (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x ↦ (g x).re) '' K) :
    TendstoUniformlyOn (cexp ∘ f ·) (cexp ∘ g) p K := by
  obtain ⟨v, hv⟩ : ∃ v, ∀ x ∈ K, (g x).re ≤ v := hg.imp <| by simp [mem_upperBounds]
  have : ∀ᶠ i in p, ∀ x ∈ K, (f i x).re ≤ v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  exact fun a ha ↦ (hv a ha).trans (lt_add_one v).le

lemma Summable.hasSumUniformlyOn_log_one_add {f : ι → α → ℂ}
    {u : ι → ℝ} (hu : Summable u) (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn (fun i x ↦ log (1 + f i x)) (fun x ↦ ∑' i, log (1 + f i x)) {K} := by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually <| hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hn' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hn').trans (by simpa using hi x hx)

lemma Summable.tendstoUniformlyOn_tsum_nat_log_one_add {f : ℕ → α → ℂ}
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun n x ↦ ∑ i ∈ Finset.range n, log (1 + f i x))
    (fun x ↦ ∑' i : ℕ, Complex.log (1 + f i x)) atTop K := by
  rw [← Nat.cofinite_eq_atTop] at h
  exact (hu.hasSumUniformlyOn_log_one_add h).tendstoUniformlyOn_finset_range rfl

end summable

section UniformlyOn

/-Note this is false without hfn. -/
lemma hasProdUniformlyOn_of_clog {f : ι → α → ℂ} {𝔖 : Set (Set α)}
    (hf : SummableUniformlyOn (fun i x ↦ log (f i x)) 𝔖) (hfn : ∀ K ∈ 𝔖, ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : ∀ K ∈ 𝔖, BddAbove <| (fun x ↦ (∑' n, log (f n x)).re) '' K) :
    HasProdUniformlyOn f (fun x ↦ ∏' i, f i x) 𝔖 := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq]
  obtain ⟨r, hr⟩ := hf.exists
  intro K hK
  suffices H : TendstoUniformlyOn (fun s a ↦ ∏ i ∈ s, f i a) (cexp ∘ r) atTop K by
    apply TendstoUniformlyOn.congr_right H
    apply Set.EqOn.trans (Set.EqOn.comp_left (hr.tsum_eqOn hK)).symm
    exact fun x hx ↦ (cexp_tsum_eq_tprod (hfn K hK x hx) (hf.summable hK hx))
  have h1 := hr.tsum_eqOn hK
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq] at hr
  refine ((hr K hK).comp_cexp ?_).congr ?_
  · simp +contextual [← h1 _]
    exact hg K hK
  · filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn K hK i hi y)]

lemma multipliableUniformlyOn_of_clog {f : ι → α → ℂ} {𝔖 : Set (Set α)}
    (hf : SummableUniformlyOn (fun i x ↦ log (f i x)) 𝔖) (hfn : ∀ K ∈ 𝔖, ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : ∀ K ∈ 𝔖, BddAbove <| (fun x ↦ (∑' n, log (f n x)).re) '' K) :
    MultipliableUniformlyOn f 𝔖 :=
    ⟨_, hasProdUniformlyOn_of_clog hf hfn hg⟩

namespace Summable

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [TopologicalSpace α]
  {f : ι → α → R} {K : Set α} {u : ι → ℝ}

lemma hasProdUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) {K} := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  by_cases hKe : K = ∅
  · simp [TendstoUniformly, hKe]
  · haveI hCK : CompactSpace K := isCompact_iff_compactSpace.mp hK
    haveI hne : Nonempty K := by rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty]
    let f' n : C(K, R) := ⟨_, continuousOn_iff_continuous_restrict.mp (hcts n)⟩
    have hf'_bd : ∀ᶠ (n : ι) in cofinite, ‖f' n‖ ≤ u n := by
      simp_rw [ContinuousMap.norm_le_of_nonempty]
      filter_upwards [h] with n hn using fun x ↦ hn x x.2
    have hM : Multipliable fun i ↦ 1 + f' i := by
      apply _root_.multipliable_one_add_of_summable
      apply hu.of_norm_bounded_eventually
      simpa only [norm_norm] using hf'_bd
    convert ContinuousMap.tendsto_iff_tendstoUniformly.mp hM.hasProd
    · aesop
    · exact funext fun k ↦ ContinuousMap.tprod_apply hM k

lemma multipliableUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableUniformlyOn (fun n x ↦ 1 + f n x) {K} :=
    ⟨_, hasProdUniformlyOn_one_add hK hu h hcts⟩

lemma hasProdUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsCompact K) {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) {K} :=
  hasProdUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

lemma multipliableUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsCompact K)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableUniformlyOn (fun n x ↦ 1 + f n x) {K} :=
  ⟨_, hasProdUniformlyOn_nat_one_add hK hu h hcts⟩

lemma hasProdLocallyUniformlyOn_one_add [LocallyCompactSpace α] (hK : IsOpen K) (hu : Summable u)
    (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdLocallyUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) K := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC ↦ hasProdUniformlyOn_one_add hC hu ?_ fun n ↦ (hcts n).mono hS
  filter_upwards [h] with n hn a ha using hn a (hS ha)

lemma multipliableLocallyUniformlyOn_one_add [LocallyCompactSpace α]
    (hK : IsOpen K) (hu : Summable u) (h : ∀ᶠ n in cofinite, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableLocallyUniformlyOn (fun n x ↦ 1 + f n x) K :=
  ⟨_, hasProdLocallyUniformlyOn_one_add hK hu h hcts⟩

lemma hasProdLocallyUniformlyOn_nat_one_add [LocallyCompactSpace α]
    {f : ℕ → α → R} (hK : IsOpen K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdLocallyUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) K := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC ↦ hasProdUniformlyOn_nat_one_add hC hu ?_ fun n ↦ (hcts n).mono hS
  filter_upwards [h] with n hn a ha using hn a (hS ha)

lemma multipliableLocallyUniformlyOn_nat_one_add [LocallyCompactSpace α]
    {f : ℕ → α → R} (hK : IsOpen K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableLocallyUniformlyOn (fun n x ↦ 1 + f n x) K :=
  ⟨_, hasProdLocallyUniformlyOn_nat_one_add hK hu h hcts⟩

end Summable

end UniformlyOn
