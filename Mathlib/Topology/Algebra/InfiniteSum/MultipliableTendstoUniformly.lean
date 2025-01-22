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

/-!
# Products of one plus a complex number

We gather some results about the uniform convergence of the product of `1 + f n x` for a
sequence `f n x` or complex numbers.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Classical Complex

variable {α β F ι: Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : ℕ → ℝ}

lemma tendstouniformlyOn_of_bounded (f : ι → α → ℝ) {p : Filter ι} (g : α → ℝ) (K : Set α) (T : ℝ)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x : α, x ∈ K → (g x) ≤ T) :
      ∃ B, ∀ᶠ (n : ι) in p, ∀ x, x ∈ K → f n x ≤ B := by
  rw [Metric.tendstoUniformlyOn_iff] at hf
  have hf2 := hf 1 (Real.zero_lt_one)
  use T + 1
  simp_rw [Filter.eventually_iff_exists_mem, dist_comm ] at *
  obtain ⟨N, hN, hN2⟩ := hf2
  refine ⟨N, hN, fun n hn x hx => ?_⟩
  apply le_trans (tsub_le_iff_right.mp (le_trans (Real.le_norm_self _) (hN2 n hn x hx).le))
  linarith [hg x hx]

lemma tendstouniformlyOn_iff_restrict {α β ι: Type*} [PseudoMetricSpace β] [Preorder ι]
    (f : ι → α → β) (g : α → β) (K : Set α) : TendstoUniformlyOn f g atTop K ↔
    TendstoUniformly (fun n : ι => K.restrict (f n)) (K.restrict g) atTop := by
  simp only [Metric.tendstoUniformlyOn_iff, gt_iff_lt, eventually_atTop, ge_iff_le, ←
    tendstoUniformlyOn_univ, Set.mem_univ, Set.restrict_apply, true_implies, Subtype.forall] at *

lemma tendstoUniformlyOn_comp_exp {α : Type*} {f : ℕ → α → ℂ} {g : α → ℂ} (K : Set α)
    (hf : TendstoUniformlyOn f g atTop K) (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (g x).re ≤ T) :
    TendstoUniformlyOn (fun n => fun x => cexp (f n x)) (cexp ∘ g) atTop K := by
  obtain ⟨T, hT⟩ := hg
  have h2 := tendstouniformlyOn_of_bounded (fun n x => (f n x).re) (fun x => (g x).re) K T
    hf.re hT
  simp only [eventually_atTop, ge_iff_le] at h2
  obtain ⟨B, δ, hδ⟩ := h2
  have w2 := tendstoUniformlyOn_univ.mpr <| UniformContinuousOn.comp_tendstoUniformly_eventually
    {x : ℂ | x.re ≤ max B T} (fun a => K.restrict (f (a))) (fun b => g b) ?_ (by aesop)
      (UniformlyContinuousOn.cexp (max B T)) (p := atTop) ?_
  · rw [tendstouniformlyOn_iff_restrict, ← tendstoUniformlyOn_univ]
    exact w2
  · simp only [Set.restrict_apply, le_max_iff, Set.mem_setOf_eq, Subtype.forall, eventually_atTop,
    ge_iff_le]
    refine ⟨δ, by aesop⟩
  · rw [tendstouniformlyOn_iff_restrict] at hf
    exact hf

lemma prod_tendstoUniformlyOn_tprod {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    (h : ∀ x : K, Summable fun n => log (f n x))
    (hf : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i in Finset.range n, log (f i a))
    (fun a : α => ∑' n : ℕ, log (f n a)) atTop K) (hfn : ∀ x : K, ∀ n : ℕ, f n x ≠ 0)
    (hg : ∃ T : ℝ, ∀ x : α, x ∈ K → (∑' n : ℕ, log (f n x)).re ≤ T) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (f i a))
    (fun a => ∏' i, (f i a)) atTop K := by
  have := TendstoUniformlyOn.congr (tendstoUniformlyOn_comp_exp K hf hg)
    (F':= (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (f i a)))
  have HU : TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (f i a))
       (cexp ∘ fun a ↦ ∑' (n : ℕ), log (f n a)) atTop K := by
      apply this
      simp only [eventually_atTop, ge_iff_le]
      refine ⟨0, fun b _ x hx => ?_⟩
      simp only [Complex.exp_sum]
      congr
      ext y
      apply Complex.exp_log (hfn ⟨x, hx⟩ y)
  apply TendstoUniformlyOn.congr_right HU
  intro x hx
  simpa using (Complex.cexp_tsum_eq_tprod _ (hfn ⟨x, hx⟩) (h ⟨x, hx⟩))

lemma prod_tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} (K : Set α)
    (hK : IsCompact K) (u : ℕ → ℝ) (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hfn : ∀ x : K, ∀ n : ℕ, 1 + f n x ≠ 0) (hcts : ∀ n, ContinuousOn (fun x => (f n x)) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i in Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  apply prod_tendstoUniformlyOn_tprod _ _ (tendstoUniformlyOn_tsum_nat_log_one_add K hu
    (Filter.Eventually.of_forall h)) hfn
  · have H : ContinuousOn (fun x ↦ (∑' (n : ℕ), Complex.log (1 + f n x)).re) K := by
      have := (tendstoUniformlyOn_tsum_nat_log_one_add K hu
        (Filter.Eventually.of_forall h)).re.continuousOn
      simp only [re_sum, eventually_atTop, ge_iff_le, forall_exists_index] at this
      apply this 0
      intro _ _
      apply continuousOn_finset_sum
      intro c _
      simp_rw [log_re]
      apply ContinuousOn.log
      · apply ContinuousOn.comp _ _ (Set.mapsTo_image (fun x ↦ 1 + f c x) K)
        · apply Continuous.continuousOn Complex.continuous_abs
        · apply (ContinuousOn.add continuousOn_const (hcts c))
      · intro z hz
        simp only [ne_eq, map_eq_zero]
        apply hfn ⟨z, hz⟩ c
    have := IsCompact.bddAbove_image hK H
    rw [@bddAbove_def] at this
    simp only [Set.mem_image, Subtype.exists, not_exists, exists_and_right, forall_exists_index,
      and_imp, Subtype.forall] at *
    obtain ⟨T, hT⟩ := this
    refine ⟨T, fun x hx => by aesop⟩
  · intro x
    apply Complex.summable_log_one_add_of_summable
    rw [← summable_norm_iff]
    apply Summable.of_nonneg_of_le (fun b ↦ norm_nonneg (f b ↑x))  (fun _ => h _ _ x.2) hu
