/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Continuity of series of functions

We prove some HasSumUniformlyOn versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions.

-/

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn_of_bounded {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x => ∑' n, f n x) {s} :=  by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn_of_cofinite_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x => ∑' n, f n x) {s} := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    (f : α → β → F) {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := (fun x => ∑' i, f i x))
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  apply tendstoUniformlyOn_tsum hu1 fun n x hx ↦ hu2 n ⟨x, hx⟩

/-- The `derivWithin` of a absolutely and uniformly converget sum on an open set `s` is the sum
of the derivatives of squence of functions on the open set `s` -/
theorem derivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] (f : α → E → F) {s : Set E}
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n , f n z) s x = ∑' n, derivWithin (fun z ↦ f n z) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (IsOpen.uniqueDiffWithinAt hs hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ Summable.hasSum (hf y hy)) hx
  · use fun n : Finset α ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ Eq.symm (HasSumLocallyUniformlyOn.tsum_eqOn hg hb)
  · filter_upwards with t r hr
    apply HasDerivAt.fun_sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · exact DifferentiableWithinAt.hasDerivWithinAt (hf2 q r hr).differentiableWithinAt
    · exact IsOpen.mem_nhds hs hr
