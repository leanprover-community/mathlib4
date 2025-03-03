/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Convex sets are null-measurable

Let `E` be a finite dimensional real vector space, let `μ` be a Haar measure on `E`, let `s` be a
convex set in `E`. Then the frontier of `s` has measure zero (see `Convex.addHaar_frontier`), hence
`s` is a `NullMeasurableSet` (see `Convex.nullMeasurableSet`).
-/


open MeasureTheory MeasureTheory.Measure Set Metric Filter Bornology

open Module (finrank)

open scoped Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {s : Set E}

namespace Convex

/-- Haar measure of the frontier of a convex set is zero. -/
theorem addHaar_frontier (hs : Convex ℝ s) : μ (frontier s) = 0 := by
  /- If `s` is included in a hyperplane, then `frontier s ⊆ closure s` is included in the same
    hyperplane, hence it has measure zero. -/
  rcases ne_or_eq (affineSpan ℝ s) ⊤ with hspan | hspan
  · refine measure_mono_null ?_ (addHaar_affineSubspace _ _ hspan)
    exact frontier_subset_closure.trans
      (closure_minimal (subset_affineSpan _ _) (affineSpan ℝ s).closed_of_finiteDimensional)
  rw [← hs.interior_nonempty_iff_affineSpan_eq_top] at hspan
  rcases hspan with ⟨x, hx⟩
  /- Without loss of generality, `s` is bounded. Indeed, `∂s ⊆ ⋃ n, ∂(s ∩ ball x (n + 1))`, hence it
    suffices to prove that `∀ n, μ (s ∩ ball x (n + 1)) = 0`; the latter set is bounded.
    -/
  suffices H : ∀ t : Set E, Convex ℝ t → x ∈ interior t → IsBounded t → μ (frontier t) = 0 by
    let B : ℕ → Set E := fun n => ball x (n + 1)
    have : μ (⋃ n : ℕ, frontier (s ∩ B n)) = 0 := by
      refine measure_iUnion_null fun n =>
        H _ (hs.inter (convex_ball _ _)) ?_ (isBounded_ball.subset inter_subset_right)
      rw [interior_inter, isOpen_ball.interior_eq]
      exact ⟨hx, mem_ball_self (add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one)⟩
    refine measure_mono_null (fun y hy => ?_) this; clear this
    set N : ℕ := ⌊dist y x⌋₊
    refine mem_iUnion.2 ⟨N, ?_⟩
    have hN : y ∈ B N := by simp [B, N, Nat.lt_floor_add_one]
    suffices y ∈ frontier (s ∩ B N) ∩ B N from this.1
    rw [frontier_inter_open_inter isOpen_ball]
    exact ⟨hy, hN⟩
  intro s hs hx hb
  /- Since `s` is bounded, we have `μ (interior s) ≠ ∞`, hence it suffices to prove
    `μ (closure s) ≤ μ (interior s)`. -/
  replace hb : μ (interior s) ≠ ∞ := (hb.subset interior_subset).measure_lt_top.ne
  suffices μ (closure s) ≤ μ (interior s) by
    rwa [frontier, measure_diff interior_subset_closure isOpen_interior.nullMeasurableSet hb,
      tsub_eq_zero_iff_le]
  /- Due to `Convex.closure_subset_image_homothety_interior_of_one_lt`, for any `r > 1` we have
    `closure s ⊆ homothety x r '' interior s`, hence `μ (closure s) ≤ r ^ d * μ (interior s)`,
    where `d = finrank ℝ E`. -/
  set d : ℕ := Module.finrank ℝ E
  have : ∀ r : ℝ≥0, 1 < r → μ (closure s) ≤ ↑(r ^ d) * μ (interior s) := fun r hr ↦ by
    refine (measure_mono <|
      hs.closure_subset_image_homothety_interior_of_one_lt hx r hr).trans_eq ?_
    rw [addHaar_image_homothety, ← NNReal.coe_pow, NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
  have : ∀ᶠ (r : ℝ≥0) in 𝓝[>] 1, μ (closure s) ≤ ↑(r ^ d) * μ (interior s) :=
    mem_of_superset self_mem_nhdsWithin this
  -- Taking the limit as `r → 1`, we get `μ (closure s) ≤ μ (interior s)`.
  refine ge_of_tendsto ?_ this
  refine (((ENNReal.continuous_mul_const hb).comp
    (ENNReal.continuous_coe.comp (continuous_pow d))).tendsto' _ _ ?_).mono_left nhdsWithin_le_nhds
  simp

/-- A convex set in a finite dimensional real vector space is null measurable with respect to an
additive Haar measure on this space. -/
protected theorem nullMeasurableSet (hs : Convex ℝ s) : NullMeasurableSet s μ :=
  nullMeasurableSet_of_null_frontier (hs.addHaar_frontier μ)

end Convex
