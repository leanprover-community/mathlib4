/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function

#align_import analysis.convex.jensen from "leanprover-community/mathlib"@"bfad3f455b388fbcc14c49d0cac884f774f14d20"

/-!
# Jensen's inequality and maximum principle for convex functions

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `Analysis.Convex.Integral`.

## Main declarations

Jensen's inequalities:
* `ConvexOn.map_centerMass_le`, `ConvexOn.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `ConcaveOn.le_map_centerMass`, `ConcaveOn.le_map_sum`: Concave Jensen's inequality.

As corollaries, we get:
* `ConvexOn.exists_ge_of_mem_convexHull`: Maximum principle for convex functions.
* `ConcaveOn.exists_le_of_mem_convexHull`: Minimum principle for concave functions.
-/


open Finset LinearMap Set

open BigOperators Classical Convex Pointwise

variable {𝕜 E F β ι : Type*}

/-! ### Jensen's inequality -/


section Jensen

variable [LinearOrderedField 𝕜] [AddCommGroup E] [OrderedAddCommGroup β] [Module 𝕜 E] [Module 𝕜 β]
  [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}

/-- Convex **Jensen's inequality**, `Finset.centerMass` version. -/
theorem ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i in t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (t.centerMass w p) ≤ t.centerMass w (f ∘ p) := by
  have hmem' : ∀ i ∈ t, (p i, (f ∘ p) i) ∈ { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := fun i hi =>
    ⟨hmem i hi, le_rfl⟩
  convert (hf.convex_epigraph.centerMass_mem h₀ h₁ hmem').2 <;>
    simp only [centerMass, Function.comp, Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]
#align convex_on.map_center_mass_le ConvexOn.map_centerMass_le

/-- Concave **Jensen's inequality**, `Finset.centerMass` version. -/
theorem ConcaveOn.le_map_centerMass (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i in t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
    t.centerMass w (f ∘ p) ≤ f (t.centerMass w p) :=
  ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem
#align concave_on.le_map_center_mass ConcaveOn.le_map_centerMass

/-- Convex **Jensen's inequality**, `Finset.sum` version. -/
theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
    (hmem : ∀ i ∈ t, p i ∈ s) : f (∑ i in t, w i • p i) ≤ ∑ i in t, w i • f (p i) := by
  simpa only [centerMass, h₁, inv_one, one_smul] using
    hf.map_centerMass_le h₀ (h₁.symm ▸ zero_lt_one) hmem
#align convex_on.map_sum_le ConvexOn.map_sum_le

/-- Concave **Jensen's inequality**, `Finset.sum` version. -/
theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    (∑ i in t, w i • f (p i)) ≤ f (∑ i in t, w i • p i) :=
  ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem
#align concave_on.le_map_sum ConcaveOn.le_map_sum

end Jensen

/-! ### Maximum principle -/


section MaximumPrinciple

variable [LinearOrderedField 𝕜] [AddCommGroup E] [LinearOrderedAddCommGroup β] [Module 𝕜 E]
  [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}
  {x : E}

theorem le_sup_of_mem_convexHull {s : Finset E} (hf : ConvexOn 𝕜 (convexHull 𝕜 (s : Set E)) f)
    (hx : x ∈ convexHull 𝕜 (s : Set E)) :
    f x ≤ s.sup' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f := by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  exact (hf.map_centerMass_le hw₀ (by positivity) <| subset_convexHull _ _).trans
    (centerMass_le_sup hw₀ <| by positivity)
#align le_sup_of_mem_convex_hull le_sup_of_mem_convexHull

theorem inf_le_of_mem_convexHull {s : Finset E} (hf : ConcaveOn 𝕜 (convexHull 𝕜 (s : Set E)) f)
    (hx : x ∈ convexHull 𝕜 (s : Set E)) :
    s.inf' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f ≤ f x :=
  le_sup_of_mem_convexHull hf.dual hx
#align inf_le_of_mem_convex_hull inf_le_of_mem_convexHull

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
theorem ConvexOn.exists_ge_of_centerMass (h : ConvexOn 𝕜 s f) (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (t.centerMass w p) ≤ f (p i) := by
  set y := t.centerMass w p
  obtain ⟨i, hi, hfi⟩ : ∃ i ∈ t.filter fun i => w i ≠ 0, w i • f y ≤ w i • (f ∘ p) i
  rotate_left
  · rw [mem_filter] at hi
    exact ⟨i, hi.1, (smul_le_smul_iff_of_pos <| (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩
  have hw' : (0 : 𝕜) < ∑ i in filter (fun i => w i ≠ 0) t, w i := by rwa [sum_filter_ne_zero]
  refine' exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') _
  rw [← sum_smul, ← smul_le_smul_iff_of_pos (inv_pos.2 hw'), inv_smul_smul₀ hw'.ne', ←
    Finset.centerMass, Finset.centerMass_filter_ne_zero]
  exact h.map_centerMass_le hw₀ hw₁ hp
#align convex_on.exists_ge_of_center_mass ConvexOn.exists_ge_of_centerMass

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
theorem ConcaveOn.exists_le_of_centerMass (h : ConcaveOn 𝕜 s f) (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) : ∃ i ∈ t, f (p i) ≤ f (t.centerMass w p) :=
  ConvexOn.exists_ge_of_centerMass (β := βᵒᵈ) h hw₀ hw₁ hp
#align concave_on.exists_le_of_center_mass ConcaveOn.exists_le_of_centerMass

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then the eventual maximum of `f` on `convexHull 𝕜 s` lies in `s`. -/
theorem ConvexOn.exists_ge_of_mem_convexHull (hf : ConvexOn 𝕜 (convexHull 𝕜 s) f) {x}
    (hx : x ∈ convexHull 𝕜 s) : ∃ y ∈ s, f x ≤ f y := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  rcases hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one) fun i hi =>
      subset_convexHull 𝕜 s (hp i hi) with
    ⟨i, hit, Hi⟩
  exact ⟨p i, hp i hit, Hi⟩
#align convex_on.exists_ge_of_mem_convex_hull ConvexOn.exists_ge_of_mem_convexHull

/-- Minimum principle for concave functions. If a function `f` is concave on the convex hull of `s`,
then the eventual minimum of `f` on `convexHull 𝕜 s` lies in `s`. -/
theorem ConcaveOn.exists_le_of_mem_convexHull (hf : ConcaveOn 𝕜 (convexHull 𝕜 s) f) {x}
    (hx : x ∈ convexHull 𝕜 s) : ∃ y ∈ s, f y ≤ f x :=
  ConvexOn.exists_ge_of_mem_convexHull (β := βᵒᵈ) hf hx
#align concave_on.exists_le_of_mem_convex_hull ConcaveOn.exists_le_of_mem_convexHull

end MaximumPrinciple
