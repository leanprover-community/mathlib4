/-
Copyright (c) 2025 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!

## Relating derivative with order

This file contains lemmas relating the derivative of functions in one variable and order.

* `exists_gt_of_deriv_pos` states that if `f` has a positive derivative at `x`, then there
  is a `z > x` such that `f y > f x` for `y` in the interval `Set.Ioc x z`. There are variations
  of this theorem in terms of `HasDerivWithinAt`, and for negative derivatives, and for finding
  points such that `f y < f x`.

## Tags

derivative
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {f : 𝕜 → 𝕜} {x y f' : 𝕜} {S : Set 𝕜}

lemma exists_gt_of_hasDerivWithinAt_pos (f'_pos : 0 < f')
    (hx : HasDerivWithinAt f f' S x) : ∃ z > x, ∀ y ∈ Set.Ioc x z ∩ S, f x < f y := by
  rw [hasDerivWithinAt_iff_tendsto_slope, tendsto_nhds] at hx
  have : slope f x ⁻¹' Set.Ioi 0 ∈ nhdsWithin x (S \ {x}) := hx (Set.Ioi 0) isOpen_Ioi f'_pos
  simp only [mem_nhdsWithin, Set.subset_def, Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_preimage, Set.mem_Ioi, and_imp] at this
  rcases this with ⟨U, U_open, x_mem_U, hU⟩
  rcases exists_Icc_mem_subset_of_mem_nhds (U_open.mem_nhds x_mem_U) with
    ⟨a, b, ⟨hax, hbx⟩, hab1, hab2⟩
  simp only [Icc_mem_nhds_iff, Set.mem_Ioo] at hab1
  refine ⟨b, hab1.2, fun y hy => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_Ioc] at hy
  have slope_pos : 0 < slope f x y :=
    hU y (hab2 ⟨le_trans hax (le_of_lt hy.1.1), by linarith⟩) hy.2 (ne_of_gt hy.1.1)
  exact (slope_pos_iff_of_le (le_of_lt hy.1.1)).1 slope_pos

lemma exists_lt_of_hasDerivWithinAt_neg (f'_neg : f' < 0)
    (hx : HasDerivWithinAt f f' S x) : ∃ z > x, ∀ y ∈ Set.Ioc x z ∩ S, f y < f x := by
  simpa using exists_gt_of_hasDerivWithinAt_pos (f := -f) (f' := -f')
    (by simpa) (by simpa using hx.const_smul (-1 : 𝕜))

open scoped Pointwise in
lemma exists_gt_of_hasDerivWithinAt_neg (f'_neg : f' < 0)
    (hx : HasDerivWithinAt f f' S x) : ∃ z < x, ∀ y ∈ Set.Ico z x ∩ S, f x < f y := by
  have := exists_gt_of_hasDerivWithinAt_pos (S := -S)
    (f := fun x => f ((-1 : 𝕜) * x)) (x := -x) (f' := (-1 : 𝕜) • f') (by simp [f'_neg]) (by
      rw [hasDerivWithinAt_comp_mul_left_smul_iff]
      simpa)
  simp only [gt_iff_lt, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_neg, mul_neg, neg_mul, one_mul,
    neg_neg, and_imp, Set.mem_Ico] at this ⊢
  rcases this with ⟨z, hzx, hz⟩
  refine ⟨-z, by linarith, fun y hxy hyz hyS => ?_⟩
  simpa using hz (-y) (by linarith) (by linarith) (by simpa using hyS)

lemma exists_lt_of_hasDerivWithinAt_pos (f'_pos : 0 < f')
    (hx : HasDerivWithinAt f f' S x) : ∃ z < x, ∀ y ∈ Set.Ico z x ∩ S, f y < f x := by
  simpa using exists_gt_of_hasDerivWithinAt_neg (f := -f) (f' := -f')
    (by simpa) (by simpa using hx.const_smul (-1 : 𝕜))

lemma exists_gt_of_derivWithin_pos (hx : 0 < derivWithin f S x) :
    ∃ z > x, ∀ y ∈ Set.Ioc x z ∩ S, f x < f y := by
  simpa using exists_gt_of_hasDerivWithinAt_pos (S := S) hx
    (hasDerivWithinAt_derivWithin_iff.2 (differentiableWithinAt_of_derivWithin_ne_zero hx.ne'))

lemma exists_lt_of_derivWithin_neg (hx : derivWithin f S x < 0) :
    ∃ z > x, ∀ y ∈ Set.Ioc x z ∩ S, f y < f x := by
  simpa using exists_lt_of_hasDerivWithinAt_neg (S := S) hx
    (hasDerivWithinAt_derivWithin_iff.2 (differentiableWithinAt_of_derivWithin_ne_zero hx.ne))

lemma exists_lt_of_derivWithin_pos (hx : 0 < derivWithin f S x) :
    ∃ z < x, ∀ y ∈ Set.Ico z x ∩ S, f y < f x := by
  simpa using exists_lt_of_hasDerivWithinAt_pos (S := S) hx
    (hasDerivWithinAt_derivWithin_iff.2 (differentiableWithinAt_of_derivWithin_ne_zero hx.ne'))

lemma exists_gt_of_derivWithin_neg (hx : derivWithin f S x < 0) :
    ∃ z < x, ∀ y ∈ Set.Ico z x ∩ S, f x < f y := by
  simpa using exists_gt_of_hasDerivWithinAt_neg (S := S) hx
    (hasDerivWithinAt_derivWithin_iff.2 (differentiableWithinAt_of_derivWithin_ne_zero hx.ne))

lemma exists_gt_of_deriv_pos (hx : 0 < deriv f x) :
    ∃ z > x, ∀ y ∈ Set.Ioc x z, f x < f y := by
  simpa using exists_gt_of_derivWithin_pos (S := Set.univ) (by simpa using hx)

lemma exists_lt_of_deriv_neg (hx : deriv f x < 0) :
    ∃ z > x, ∀ y ∈ Set.Ioc x z, f y < f x := by
  simpa using exists_gt_of_deriv_pos (f := -f) (by simpa)

lemma exists_lt_of_deriv_pos (hx : 0 < deriv f x) :
    ∃ z < x, ∀ y ∈ Set.Ico z x, f y < f x := by
  simpa using exists_lt_of_derivWithin_pos (S := Set.univ) (by simpa using hx)

lemma exists_gt_of_deriv_neg (hx : deriv f x < 0) :
    ∃ z < x, ∀ y ∈ Set.Ico z x, f x < f y := by
  simpa using exists_lt_of_deriv_pos (f := -f) (by simpa)
