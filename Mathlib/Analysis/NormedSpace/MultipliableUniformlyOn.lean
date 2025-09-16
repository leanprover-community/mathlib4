/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# Uniform convergence of products of functions

We gather some results about the uniform convergence of infinite products, in particular those of
the form `∏' i, (1 + f i x)` for a sequence `f` of complex-valued functions.
-/

open Filter Function Complex Finset Topology

variable {α ι : Type*} {𝔖 : Set (Set α)} {K : Set α} {u : ι → ℝ}

section Complex

variable {f : ι → α → ℂ}

lemma TendstoUniformlyOn.comp_cexp {p : Filter ι} {g : α → ℂ}
    (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x ↦ (g x).re) '' K) :
    TendstoUniformlyOn (cexp ∘ f ·) (cexp ∘ g) p K := by
  obtain ⟨v, hv⟩ : ∃ v, ∀ x ∈ K, (g x).re ≤ v := hg.imp <| by simp [mem_upperBounds]
  have : ∀ᶠ i in p, ∀ x ∈ K, (f i x).re ≤ v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  exact fun x hx ↦ (hv x hx).trans (lt_add_one v).le

lemma Summable.hasSumUniformlyOn_log_one_add (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) :
    HasSumUniformlyOn (fun i x ↦ log (1 + f i x)) (fun x ↦ ∑' i, log (1 + f i x)) {K} := by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff, forall_eq]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually <| hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hi' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hi').trans (by simpa using hi x hx)

lemma Summable.tendstoUniformlyOn_tsum_nat_log_one_add {f : ℕ → α → ℂ} {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun n x ↦ ∑ m ∈ Finset.range n, log (1 + f m x))
    (fun x ↦ ∑' n, log (1 + f n x)) atTop K := by
  rw [← Nat.cofinite_eq_atTop] at h
  exact (hu.hasSumUniformlyOn_log_one_add h).tendstoUniformlyOn_finsetRange rfl

/-- If `x ↦ ∑' i, log (f i x)` is uniformly convergent on `𝔖`, its sum has bounded-above real part
on each set in `𝔖`, and the functions `f i x` have no zeroes, then  `∏' i, f i x` is uniformly
convergent on `𝔖`.

Note that the non-vanishing assumption is really needed here: if this assumption is dropped then
one obtains a counterexample if `ι = α = ℕ` and `f i x` is `0` if `i = x` and `1` otherwise. -/
lemma hasProdUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x ↦ log (f i x)) 𝔖)
    (hfn : ∀ K ∈ 𝔖, ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : ∀ K ∈ 𝔖, BddAbove <| (fun x ↦ (∑' i, log (f i x)).re) '' K) :
    HasProdUniformlyOn f (fun x ↦ ∏' i, f i x) 𝔖 := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  obtain ⟨r, hr⟩ := hf.exists
  intro K hK
  suffices H : TendstoUniformlyOn (fun s x ↦ ∏ i ∈ s, f i x) (cexp ∘ r) atTop K by
    refine H.congr_right ((hr.tsum_eqOn hK).comp_left.symm.trans ?_)
    exact fun x hx ↦ (cexp_tsum_eq_tprod (hfn K hK x hx) (hf.summable hK hx))
  have h1 := hr.tsum_eqOn hK
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn] at hr
  refine ((hr K hK).comp_cexp ?_).congr ?_
  · simp +contextual [← h1 _]
    exact hg K hK
  · filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn K hK i hi y)]

lemma multipliableUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x ↦ log (f i x)) 𝔖)
    (hfn : ∀ K ∈ 𝔖, ∀ x ∈ K, ∀ i, f i x ≠ 0)
    (hg : ∀ K ∈ 𝔖, BddAbove <| (fun x ↦ (∑' i, log (f i x)).re) '' K) :
    MultipliableUniformlyOn f 𝔖 :=
  ⟨_, hasProdUniformlyOn_of_clog hf hfn hg⟩

end Complex

namespace Summable

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [TopologicalSpace α]
  {f : ι → α → R}

/-- If a sequence of continuous functions `f i x` on an open compact `K` have norms eventually
bounded by a summable function, then `∏' i, (1 + f i x)` is uniformly convergent on `K`. -/
lemma hasProdUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    HasProdUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) {K} := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, forall_eq]
  by_cases hKe : K = ∅
  · simp [TendstoUniformly, hKe]
  · haveI hCK : CompactSpace K := isCompact_iff_compactSpace.mp hK
    haveI hne : Nonempty K := by rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty]
    let f' i : C(K, R) := ⟨_, continuousOn_iff_continuous_restrict.mp (hcts i)⟩
    have hf'_bd : ∀ᶠ i in cofinite, ‖f' i‖ ≤ u i := by
      simp only [ContinuousMap.norm_le_of_nonempty]
      filter_upwards [h] with i hi using fun x ↦ hi x x.2
    have hM : Multipliable fun i ↦ 1 + f' i :=
      multipliable_one_add_of_summable (hu.of_norm_bounded_eventually (by simpa using hf'_bd))
    convert ContinuousMap.tendsto_iff_tendstoUniformly.mp hM.hasProd
    · simp [f']
    · exact funext fun k ↦ ContinuousMap.tprod_apply hM k

lemma multipliableUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    MultipliableUniformlyOn (fun i x ↦ 1 + f i x) {K} :=
  ⟨_, hasProdUniformlyOn_one_add hK hu h hcts⟩

/-- This is a version of `hasProdUniformlyOn_one_add` for sequences indexed by `ℕ`. -/
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

section LocallyCompactSpace

variable [LocallyCompactSpace α]

/-- If a sequence of continuous functions `f i x` on an open subset `K` have norms eventually
bounded by a summable function, then `∏' i, (1 + f i x)` is locally uniformly convergent on `K`. -/
lemma hasProdLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) K := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC ↦ hasProdUniformlyOn_one_add hC hu ?_ fun i ↦ (hcts i).mono hS
  filter_upwards [h] with i hi a ha using hi a (hS ha)

lemma multipliableLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    MultipliableLocallyUniformlyOn (fun i x ↦ 1 + f i x) K :=
  ⟨_, hasProdLocallyUniformlyOn_one_add hK hu h hcts⟩

/-- This is a version of `hasProdLocallyUniformlyOn_one_add` for sequences indexed by `ℕ`. -/
lemma hasProdLocallyUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsOpen K) {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdLocallyUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) K :=
  hasProdLocallyUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts

lemma multipliableLocallyUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsOpen K) {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableLocallyUniformlyOn (fun n x ↦ 1 + f n x) K :=
  ⟨_, hasProdLocallyUniformlyOn_nat_one_add hK hu h hcts⟩

end LocallyCompactSpace

end Summable
