/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FieldSimp

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
* `StrictConvexOn.map_sum_lt`: Convex strict Jensen inequality.
* `StrictConcaveOn.lt_map_sum`: Concave strict Jensen inequality.

As corollaries, we get:
* `StrictConvexOn.map_sum_eq_iff`: Equality case of the convex Jensen inequality.
* `StrictConcaveOn.map_sum_eq_iff`: Equality case of the concave Jensen inequality.
* `ConvexOn.exists_ge_of_mem_convexHull`: Maximum principle for convex functions.
* `ConcaveOn.exists_le_of_mem_convexHull`: Minimum principle for concave functions.
-/


open Finset LinearMap Set

open BigOperators Classical Convex Pointwise

variable {𝕜 E F β ι : Type*}

/-! ### Jensen's inequality -/


section Jensen

variable [LinearOrderedField 𝕜] [AddCommGroup E] [OrderedAddCommGroup β] [Module 𝕜 E] [Module 𝕜 β]
  [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E} {v : 𝕜} {q : E}

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

/-- Convex **Jensen's inequality** where an element plays a distinguished role. -/
lemma ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    f (v • q + ∑ i in t, w i • p i) ≤ v • f q + ∑ i in t, w i • f (p i) := by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j in insertNone t, W j • P j) ≤ ∑ j in insertNone t, W j • f (P j) :=
    hf.map_sum_le (forall_mem_insertNone.2 ⟨hv, h₀⟩) (by simpa using h₁)
      (forall_mem_insertNone.2 ⟨hq, hmem⟩)
  simpa using this

/-- Concave **Jensen's inequality** where an element plays a distinguished role. -/
lemma ConcaveOn.map_add_sum_le (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    v • f q + ∑ i in t, w i • f (p i) ≤ f (v • q + ∑ i in t, w i • p i) :=
  hf.dual.map_add_sum_le h₀ h₁ hmem hv hq

/-! ### Strict Jensen inequality -/

/-- Convex **strict Jensen inequality**.

If the function is strictly convex, the weights are strictly positive and the indexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConvexOn.map_sum_eq_iff`. -/
lemma StrictConvexOn.map_sum_lt (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) := by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  -- We replace `t` by `t \ {j, k}`
  have : k ∈ t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp
  have hk : k ∉ u := by simp
  have ht : t = (u.cons k hk).cons j (mem_cons.not.2 <| not_or_intro (ne_of_apply_ne _ hjk) hj)
  · simp [insert_erase this, insert_erase ‹j ∈ t›, *]
  clear_value u
  subst ht
  simp only [sum_cons]
  have := h₀ j <| by simp
  have := h₀ k <| by simp
  let c := w j + w k
  have hc : w j / c + w k / c = 1 := by field_simp
  have hcj : c * (w j / c) = w j := by field_simp; ring
  have hck : c * (w k / c) = w k := by field_simp; ring
  calc f (w j • p j + (w k • p k + ∑ x in u, w x • p x))
    _ = f (c • ((w j / c) • p j + (w k / c) • p k) + ∑ x in u, w x • p x) := by
      rw [smul_add, ← mul_smul, ← mul_smul, hcj, hck, add_assoc]
    _ ≤ c • f ((w j / c) • p j + (w k / c) • p k) + ∑ x in u, w x • f (p x) :=
      -- apply the usual Jensen's inequality wrt the weighted average of the two distinguished
      -- points and all the other points
        hf.convexOn.map_add_sum_le (fun i hi ↦ (h₀ _ <| by simp [hi]).le)
          (by simpa [-cons_eq_insert, ← add_assoc] using h₁)
          (forall_of_forall_cons <| forall_of_forall_cons hmem) (by positivity) <| by
           refine hf.1 (hmem _ <| by simp) (hmem _ <| by simp) ?_ ?_ hc <;> positivity
    _ < c • ((w j / c) • f (p j) + (w k / c) • f (p k)) + ∑ x in u, w x • f (p x) := by
      -- then apply the definition of strict convexity for the two distinguished points
      gcongr; refine hf.2 (hmem _ <| by simp) (hmem _ <| by simp) hjk ?_ ?_ hc <;> positivity
    _ = (w j • f (p j) + w k • f (p k)) + ∑ x in u, w x • f (p x) := by
      rw [smul_add, ← mul_smul, ← mul_smul, hcj, hck]
    _ = w j • f (p j) + (w k • f (p k) + ∑ x in u, w x • f (p x)) := by abel_nf

/-- Concave **strict Jensen inequality**.

If the function is strictly concave, the weights are strictly positive and the indexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConcaveOn.map_sum_eq_iff`. -/
lemma StrictConcaveOn.lt_map_sum (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) := hf.dual.map_sum_lt h₀ h₁ hmem hp

/-! ### Equality case of Jensen's inequality -/

/-- A form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, if
`f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)`, then the points `p` are all equal.

See also `StrictConvexOn.map_sum_eq_iff`. -/
lemma StrictConvexOn.eq_of_le_map_sum (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : ∑ i in t, w i • f (p i) ≤ f (∑ i in t, w i • p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  by_contra!; exact h_eq.not_lt <| hf.map_sum_lt h₀ h₁ hmem this

/-- A form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, if
`f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)`, then the points `p` are all equal.

See also `StrictConcaveOn.map_sum_eq_iff`. -/
lemma StrictConcaveOn.eq_of_map_sum_eq (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : f (∑ i in t, w i • p i) ≤ ∑ i in t, w i • f (p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  by_contra!; exact h_eq.not_lt <| hf.lt_map_sum h₀ h₁ hmem this

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, we have
`f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)` if and only if the points `p` are all equal
(and in fact all equal to their center of mass wrt `w`). -/
lemma StrictConvexOn.map_sum_eq_iff {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i in t, w i • p i := by
  constructor
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H : ∀ j ∈ t, p j = p i₀ := by
      intro j hj
      apply hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1:𝕜) • p i₀ := by simp
      _ = (∑ j in t, w j) • p i₀ := by rw [h₁]
      _ = ∑ j in t, (w j • p i₀) := by rw [sum_smul]
      _ = ∑ j in t, (w j • p j) := by congr! 2 with j hj; rw [← H _ hj]
  · intro h
    have H : ∀ j ∈ t, w j • f (p j) = w j • f (∑ i in t, w i • p i) := by
      intro j hj
      simp [h j hj]
    rw [sum_congr rfl H, ← sum_smul, h₁, one_smul]

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, we have
`f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)` if and only if the points `p` are all equal
(and in fact all equal to their center of mass wrt `w`). -/
lemma StrictConcaveOn.map_sum_eq_iff (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i in t, w i • p i := by
  simpa using hf.neg.map_sum_eq_iff h₀ h₁ hmem

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and nonnegative weights `w`, we have
`f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)` if and only if the points `p` with nonzero
weight are all equal (and in fact all equal to their center of mass wrt `w`). -/
lemma StrictConvexOn.map_sum_eq_iff' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i in t, w i • p i := by
  have hw (i) (_ : i ∈ t) : w i • p i ≠ 0 → w i ≠ 0 := by aesop
  have hw' (i) (_ : i ∈ t) : w i • f (p i) ≠ 0 → w i ≠ 0 := by aesop
  rw [← sum_filter_of_ne hw, ← sum_filter_of_ne hw', hf.map_sum_eq_iff]
  · simp
  · simp (config := { contextual := true }) [(h₀ _ _).gt_iff_ne]
  · rwa [sum_filter_ne_zero]
  · simp (config := { contextual := true }) [hmem _ _]

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and nonnegative weights `w`, we have
`f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i)` if and only if the points `p` with nonzero
weight are all equal (and in fact all equal to their center of mass wrt `w`). -/
lemma StrictConcaveOn.map_sum_eq_iff' (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i in t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i in t, w i • p i := hf.dual.map_sum_eq_iff' h₀ h₁ hmem

end Jensen

/-! ### Maximum principle -/


section MaximumPrinciple

variable [LinearOrderedField 𝕜] [AddCommGroup E] [LinearOrderedAddCommGroup β] [Module 𝕜 E]
  [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}
  {x y z : E}

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
    exact ⟨i, hi.1, (smul_le_smul_iff_of_pos_left <| (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩
  have hw' : (0 : 𝕜) < ∑ i in filter (fun i => w i ≠ 0) t, w i := by rwa [sum_filter_ne_zero]
  refine' exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') _
  rw [← sum_smul, ← smul_le_smul_iff_of_pos_left (inv_pos.2 hw'), inv_smul_smul₀ hw'.ne', ←
    centerMass, centerMass_filter_ne_zero]
  exact h.map_centerMass_le hw₀ hw₁ hp
#align convex_on.exists_ge_of_center_mass ConvexOn.exists_ge_of_centerMass

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
theorem ConcaveOn.exists_le_of_centerMass (h : ConcaveOn 𝕜 s f) (hw₀ : ∀ i ∈ t, 0 ≤ w i)
    (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) : ∃ i ∈ t, f (p i) ≤ f (t.centerMass w p) :=
  ConvexOn.exists_ge_of_centerMass (β := βᵒᵈ) h hw₀ hw₁ hp
#align concave_on.exists_le_of_center_mass ConcaveOn.exists_le_of_centerMass

/-- **Maximum principle** for convex functions. If a function `f` is convex on the convex hull of
`s`, then the eventual maximum of `f` on `convexHull 𝕜 s` lies in `s`. -/
theorem ConvexOn.exists_ge_of_mem_convexHull (hf : ConvexOn 𝕜 (convexHull 𝕜 s) f) {x}
    (hx : x ∈ convexHull 𝕜 s) : ∃ y ∈ s, f x ≤ f y := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  rcases hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one) fun i hi =>
      subset_convexHull 𝕜 s (hp i hi) with
    ⟨i, hit, Hi⟩
  exact ⟨p i, hp i hit, Hi⟩
#align convex_on.exists_ge_of_mem_convex_hull ConvexOn.exists_ge_of_mem_convexHull

/-- **Minimum principle** for concave functions. If a function `f` is concave on the convex hull of
`s`, then the eventual minimum of `f` on `convexHull 𝕜 s` lies in `s`. -/
theorem ConcaveOn.exists_le_of_mem_convexHull (hf : ConcaveOn 𝕜 (convexHull 𝕜 s) f) {x}
    (hx : x ∈ convexHull 𝕜 s) : ∃ y ∈ s, f y ≤ f x :=
  ConvexOn.exists_ge_of_mem_convexHull (β := βᵒᵈ) hf hx
#align concave_on.exists_le_of_mem_convex_hull ConcaveOn.exists_le_of_mem_convexHull

/-- **Maximum principle** for convex functions on a segment. If a function `f` is convex on the
segment `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 [x -[𝕜] y] f) (hz : z ∈ [x -[𝕜] y]) :
    f z ≤ max (f x) (f y) := by
  rw [← convexHull_pair] at hf hz; simpa using hf.exists_ge_of_mem_convexHull hz

/-- **Minimum principle** for concave functions on a segment. If a function `f` is concave on the
segment `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 [x -[𝕜] y] f) (hz : z ∈ [x -[𝕜] y]) :
    min (f x) (f y) ≤ f z := by
  rw [← convexHull_pair] at hf hz; simpa using hf.exists_le_of_mem_convexHull hz

/-- **Maximum principle** for convex functions on an interval. If a function `f` is convex on the
interval `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConvexOn.le_max_of_mem_Icc {f : 𝕜 → β} {x y z : 𝕜} (hf : ConvexOn 𝕜 (Icc x y) f)
    (hz : z ∈ Icc x y) : f z ≤ max (f x) (f y) := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hf hz; exact hf.le_max_of_mem_segment hz

/-- **Minimum principle** for concave functions on an interval. If a function `f` is concave on the
interval `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConcaveOn.min_le_of_mem_Icc {f : 𝕜 → β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 (Icc x y) f)
    (hz : z ∈ Icc x y) : min (f x) (f y) ≤ f z := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hf hz; exact hf.min_le_of_mem_segment hz

end MaximumPrinciple
