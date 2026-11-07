/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Differentiability of sum of functions

We prove some `HasSumUniformlyOn` versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions we also prove an `iteratedDerivWithin`
version.

-/

public section

open Set TopologicalSpace Filter

open scoped Topology NNReal

section UniformlyOn

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn.of_norm_le_summable {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
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

section Differentiable

variable {ι F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedAddCommGroup F] [NormedSpace E F] {s : Set E} {f : ι → E → F} {x : E}

/-- If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z` in an
open set `s`, and `∑ (derivWithin fₙ s) (z)` is summable locally uniformly on `s`, and each `fₙ` is
differentiable, then `∑ fₙ` is differentiable at each point in `s`. -/
theorem SummableLocallyUniformlyOn.hasDerivAt_tsum (hs : IsOpen s) (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (f n) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    HasDerivAt (fun z => ∑' (n : ι), f n z) (∑' (n : ι), derivWithin (f n) s x) x := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ (hf y hy).hasSum) hx
    (f' := fun n : Finset ι ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq ↦ ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

/-- If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z` in an
open set `s`, and `∑ (derivWithin fₙ s) (z)` is summable locally uniformly on `s`, and each `fₙ` is
differentiable, then `∑ fₙ` is differentiable on `s`. -/
theorem SummableLocallyUniformlyOn.differentiableOn_tsum (hs : IsOpen s)
    (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (f n) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    DifferentiableOn E (fun z => ∑' (n : ι), f n z) s :=
  fun _ hx => (h.hasDerivAt_tsum hs hx hf hf2).hasDerivWithinAt.differentiableWithinAt

/-- The `derivWithin` of a sum whose derivative is summable locally uniformly on an open set `s`
is the sum of the derivatives of sequence of functions on the open set `s` -/
theorem SummableLocallyUniformlyOn.derivWithin_tsum (hs : IsOpen s) (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (f n) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n, f n z) s x = ∑' n, derivWithin (f n) s x :=
  (h.hasDerivAt_tsum hs hx hf hf2).hasDerivWithinAt.derivWithin (hs.uniqueDiffWithinAt hx)

@[deprecated (since := "2026-10-30")]
alias derivWithin_tsum := SummableLocallyUniformlyOn.derivWithin_tsum

/-- If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z` in an
open set `s`, and for each `1 ≤ k ≤ m`, the series of `k`-th iterated derivatives
`∑ (iteratedDerivWithin k fₙ s) (z)` is summable locally uniformly on `s`, and each `fₙ` is
`m`-times differentiable, then the `m`-th iterated derivative of the sum is the sum of the
`m`-th iterated derivatives. -/
theorem SummableLocallyUniformlyOn.iteratedDerivWithin_tsum (m : ℕ) (hs : IsOpen s) (hx : x ∈ s)
    (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t))
    (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (f n) s)) s)
    (hf2 : ∀ n k r, k < m → r ∈ s → DifferentiableAt E (iteratedDerivWithin k (f n) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← SummableLocallyUniformlyOn.derivWithin_tsum hs hx _ _
      (fun n r hr ↦ hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht ↦ hm ht (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ ↦ by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht ↦ by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))

@[deprecated (since := "2026-10-30")]
alias iteratedDerivWithin_tsum := SummableLocallyUniformlyOn.iteratedDerivWithin_tsum

/-- If a sequence of functions `fₙ` is such that for each `0 ≤ k ≤ N`, the series of `k`-th
iterated derivatives `∑ (iteratedDerivWithin k fₙ s) (z)` is summable locally uniformly on `s`, and
each `fₙ` is in the class of `C^N`, then the series is also in `C^N`. -/
theorem SummableLocallyUniformlyOn.contDiffOn_tsum {N : ℕ∞} (hs : IsOpen s)
    (hf : ∀ (n : ι), ContDiffOn E N (f n) s)
    (h : ∀ (k : ℕ), k ≤ N → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (f n) s)) s) :
    ContDiffOn E N (fun (x : E) => ∑' (n : ι), f n x) s := by
  simp_all only [contDiffOn_iff_continuousOn_differentiableOn_deriv hs.uniqueDiffOn]
  have q (r : E) (hr : r ∈ s) : s ∈ 𝓝 r := hs.mem_nhds hr
  have hsum : ∀ t ∈ s, Summable fun (n : ι) => f n t := fun t ht => (h 0 zero_le).summable ht
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · refine ((h m hm).continuousOn_tsum (fun i => (hf i).1 m hm)).congr (fun x hx => ?_)
    · refine SummableLocallyUniformlyOn.iteratedDerivWithin_tsum m hs hx hsum (fun k _ hk => ?_)
        (fun n k r hk hr => ?_)
      · exact h k (LE.le.trans (mod_cast hk) hm)
      · exact ((hf n).2 k (lt_of_lt_of_le (mod_cast hk) hm)).differentiableAt (q r hr)
  · have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using Order.add_one_le_of_lt hm
    refine DifferentiableOn.congr (f := fun x => ∑' n, iteratedDerivWithin m (f n) s x) ?_
      (fun x hx => ?_)
    · refine SummableLocallyUniformlyOn.differentiableOn_tsum hs (fun y hy =>
        (h m hm.le).summable hy) ?_ (fun n r hr => ((hf n).2 m hm).differentiableAt (q r hr))
      refine SummableLocallyUniformlyOn_congr (fun n x hx => ?_) (h (m + 1) h'm)
      rw [← iteratedDerivWithin_succ]
    · refine SummableLocallyUniformlyOn.iteratedDerivWithin_tsum m hs hx hsum (fun k _ hk => ?_)
        (fun n k r hk hr => ?_)
      · exact h k (le_trans (mod_cast hk) hm.le)
      · exact ((hf n).2 k (lt_trans (mod_cast hk) hm)).differentiableAt (q r hr)

end Differentiable
