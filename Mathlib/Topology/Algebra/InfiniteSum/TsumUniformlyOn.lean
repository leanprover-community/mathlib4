/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of sum of functions

We prove some `HasSumUniformlyOn` versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions we also prove an `iteratedDerivWithin`
version.

-/

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

section UniformlyOn

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn.of_norm_le_summable {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) {s} :=  by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) {s} := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

lemma SummableLocallyUniformlyOn.of_locally_bounded_eventually [TopologicalSpace β]
    [LocallyCompactSpace β] {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧
    ∀ᶠ n in cofinite, ∀ k ∈ K, ‖f n k‖ ≤ u n) : SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x ↦ ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n, ∀ k ∈ K, ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

end UniformlyOn

variable {ι F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedAddCommGroup F] [NormedSpace E F] {s : Set E}

/-- The `derivWithin` of a sum whose derivative is absolutely and uniformly convergent sum on an
open set `s` is the sum of the derivatives of sequence of functions on the open set `s` -/
theorem derivWithin_tsum {f : ι → E → F} (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n, f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ (hf y hy).hasSum) hx
    (f' := fun n : Finset ι ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq ↦ ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

/-- If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z` in an
open set `s`, and for each `1 ≤ k ≤ m`, the series of `k`-th iterated derivatives
`∑ (iteratedDerivWithin k fₙ s) (z)`
is summable locally uniformly on `s`, and each `fₙ` is `m`-times differentiable, then the `m`-th
iterated derivative of the sum is the sum of the `m`-th iterated derivatives. -/
theorem iteratedDerivWithin_tsum {f : ι → E → F} (m : ℕ) (hs : IsOpen s)
    {x : E} (hx : x ∈ s) (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t))
    (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, k ≤ m → r ∈ s →
      DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _  _ (fun n r hr ↦ hf2 n m r (by cutsat) hr)]
    · exact derivWithin_congr (fun t ht ↦ hm ht (fun k hk1 hkm ↦ h k hk1 (by cutsat))
          (fun k r e hr he ↦ hf2 k r e (by cutsat) he)) (hm hx (fun k hk1 hkm ↦ h k hk1 (by cutsat))
          (fun k r e hr he ↦ hf2 k r e (by cutsat) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by cutsat) (by cutsat)).summable hr).congr (fun _ ↦ by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht ↦ iteratedDerivWithin_succ) (h (m + 1) (by cutsat) (by cutsat))
