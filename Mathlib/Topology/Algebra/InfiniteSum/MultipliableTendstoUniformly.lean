/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.ToAdditive

/-!
# Products of one plus a complex number

We gather some results about the uniform convergence of the product of `1 + f n x` for a
sequence `f n x` of complex numbers.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Complex

variable {α β ι : Type*}

@[to_additive] --what do I call this?
lemma TendstoUniformlyOn_Eventually_lt_mul_const [UniformSpace β] [Group β]
    [UniformGroup β] [LinearOrder β] [OrderTopology β] [MulLeftStrictMono β] [MulRightMono β]
    (f : ι → α → β)  {p : Filter ι} {g : α → β} {K : Set α} {T V : β} (htv : T < V)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x, x ∈ K → g x ≤ T) :
    ∀ᶠ (n : ι) in p, ∀ x, x ∈ K → f n x < V := by
  rw [@tendstoUniformlyOn_iff_tendsto] at hf
  simp only [uniformity_eq_comap_inv_mul_nhds_one, tendsto_iff_eventually, eventually_comap,
    Prod.forall, uniformContinuous_def, mem_comap, forall_exists_index, and_imp] at *
  rw [Subtype.forall'] at hf
  have hf2 := hf ⟨(fun x : β × β => x.1⁻¹ * x.2 < T⁻¹ * V), by
    rw [eventually_iff_exists_mem]
    refine ⟨{ x : β | x < T⁻¹ * V }, IsOpen.mem_nhds (isOpen_gt' (T⁻¹ * V)) (by simp [htv]) ,
      fun y hy a b hab => ?_⟩
    simpa only [Subtype.forall, lt_inv_mul_iff_mul_lt, Set.mem_setOf_eq, hab] using hy⟩
  rw [eventually_prod_principal_iff, eventually_iff_exists_mem] at *
  obtain ⟨v, hv, H⟩ := hf2
  refine ⟨v, hv, fun y hy x hx => ?_⟩
  simpa using (mul_lt_mul_of_le_of_lt (hg x hx) (H y hy x hx))

@[to_additive] --what do I call this? and is there an easier way to get this from the above?
lemma TendstoUniformlyOn_Eventually_le_mul_const [UniformSpace β] [Group β]
    [UniformGroup β] [LinearOrder β] [OrderTopology β] [MulLeftStrictMono β] [MulRightMono β]
    (f : ι → α → β)  {p : Filter ι} {g : α → β} {K : Set α} {T V : β} (htv : T < V)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x, x ∈ K → g x ≤ T) :
    ∀ᶠ (n : ι) in p, ∀ x, x ∈ K → f n x ≤ V := by
    have := TendstoUniformlyOn_Eventually_lt_mul_const f htv hf hg
    rw [eventually_iff_exists_mem] at *
    obtain ⟨v, hv, H⟩ := this
    refine ⟨v, hv, fun n hn x hx => (H n hn x hx).le⟩

lemma tendstoUniformlyOn_comp_cexp {p : Filter ι} {f : ι → α → ℂ} {g : α → ℂ}
    {K : Set α} (hf : TendstoUniformlyOn f g p K) (hg : BddAbove ((fun x => (g x).re) '' K)) :
    TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) p K := by
  obtain ⟨T, hT⟩ := hg
  simp only [mem_upperBounds, Set.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hT
  have h2 := TendstoUniformlyOn_Eventually_le_add_const (fun n x => (f n x).re) (lt_add_one T)
    hf.re hT
  have w2 := tendstoUniformlyOn_univ.mpr <| UniformContinuousOn.comp_tendstoUniformly_eventually
    {x : ℂ | x.re ≤ T + 1} (fun a => K.restrict (f (a))) (fun b => g b) (by simpa using h2) ?_
      (UniformContinuousOn.cexp (T + 1)) ((tendstouniformlyOn_iff_restrict).mp hf)
  · rw [tendstouniformlyOn_iff_restrict, ← tendstoUniformlyOn_univ]
    exact w2
  · simp only [Set.mem_setOf_eq, Subtype.forall]
    apply fun a ha => le_trans (hT a ha) (by aesop)

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
  simp only [eventually_atTop, ge_iff_le]
  refine ⟨⊥, fun b _ x hx => ?_⟩
  simp only [Complex.exp_sum]
  congr
  exact funext fun y ↦ Complex.exp_log (hfn x hx y)

/-- This is a version for nat that uses range in the products. -/
lemma tendstoUniformlyOn_tprod_nat_of_clog {f : ℕ → α → ℂ} {K : Set α}
    (h : ∀ x, x ∈ K → Summable fun n => log (f n x))
    (hf : TendstoUniformlyOn (fun n a => ∑ i ∈ n, log (f i a)) (fun a : α => ∑' n : ℕ, log (f n a))
    atTop K) (hfn : ∀ x, x ∈ K → ∀ n : ℕ, f n x ≠ 0)
    (hg : BddAbove ((fun x => (∑' n : ℕ, log (f n x)).re) '' K)) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (f i a))
    (fun a => ∏' i, (f i a)) atTop K :=
  fun v hv => tendsto_finset_range.eventually (tendstoUniformlyOn_tprod_of_clog h hf hfn hg v hv)

/-- This is the version for infinite products of with terms of the from `1 + f n x`. -/
lemma tendstoUniformlyOn_tprod_nat [TopologicalSpace α] {f : ℕ → α → ℂ} {K : Set α}
    (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hfn : ∀ x, x ∈ K → ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  apply tendstoUniformlyOn_tprod_nat_of_clog ?_ ?_ hfn
  · have H : ContinuousOn (fun x ↦ (∑' (n : ℕ), Complex.log (1 + f n x)).re) K := by
      apply (tendstoUniformlyOn_tsum_nat_log_one_add K hu
        (Filter.Eventually.of_forall h)).re.continuousOn
      simp only [re_sum, eventually_atTop, ge_iff_le]
      refine ⟨0, fun _ _ _ => ?_⟩
      apply continuousOn_finset_sum
      intro c _
      simp_rw [log_re]
      apply ContinuousOn.log
      · apply ContinuousOn.comp continuous_norm.continuousOn
          (ContinuousOn.add continuousOn_const (hcts c)) (Set.mapsTo_image (fun x ↦ 1 + f c x) K)
      · intro z hz
        simpa using hfn z hz c
    apply IsCompact.bddAbove_image hK H
  · intro x hx
    apply Complex.summable_log_one_add_of_summable (summable_norm_iff.mp
      (Summable.of_nonneg_of_le (fun b ↦ norm_nonneg (f b ↑x)) (fun _ => h _ _ hx) hu))
  · apply Complex.tendstoUniformlyOn_tsum_log_one_add K hu (Filter.Eventually.of_forall h)

/-- This is the locally version for infinite products of with terms of the from `1 + f n x`. -/
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
