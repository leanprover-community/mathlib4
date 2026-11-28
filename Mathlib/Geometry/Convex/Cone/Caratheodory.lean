/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Carathéodory's theorem for cones

Every point in the conic hull of a set `s` lies in the conic hull of a finite linearly independent
subset of `s`. See also `convexHull_eq_union` for the convex hull version.

## Main results

* `PointedCone.hull_eq_union`: the conical version of Carathéodory's theorem.
-/

@[expose] public section

open Set Finset

universe u

variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {s : Set E} {x : E}

namespace PointedCone

/-- If `x` is in the conic hull of some finset `t` whose elements are not linearly independent,
then it is in the conic hull of a strict subset of `t`. -/
theorem mem_hull_erase [DecidableEq E] {t : Finset E} (h : ¬LinearIndepOn 𝕜 id (t : Set E))
    (hx : x ∈ hull 𝕜 (t : Set E)) : ∃ y ∈ t, x ∈ hull 𝕜 (t.erase y : Set E) := by
  obtain ⟨f, -, fpos, rfl⟩ := mem_hull_finset.mp hx
  obtain ⟨g, gcombo, i, hi, hgi⟩ : ∃ g : E → 𝕜, ∑ e ∈ t, g e • e = 0 ∧ ∃ i ∈ t, 0 < g i := by
    obtain ⟨g, gcombo, i, hi, hgi⟩ := not_linearIndepOn_finset_iff.mp h
    rcases hgi.lt_or_gt with hgi | hgi
    · exact ⟨-g, by simpa [neg_smul, sum_neg_distrib] using gcombo, i, hi, neg_pos.mpr hgi⟩
    · exact ⟨g, gcombo, i, hi, hgi⟩
  let s : Finset E := {z ∈ t | 0 < g z}
  obtain ⟨i₀, mem, w⟩ := exists_min_image s (fun z ↦ f z / g z) ⟨i, mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨hi₀, hg⟩ := mem_filter.mp mem
  let k : E → 𝕜 := fun z ↦ f z - f i₀ / g i₀ * g z
  have hk : k i₀ = 0 := by simp [k, hg.ne']
  have hsum : ∑ e ∈ t.erase i₀, k e • e = ∑ e ∈ t, f e • e := by
    rw [sum_erase _ (by simp [hk])]
    simp_rw [k, sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, gcombo, smul_zero, sub_zero]
  refine ⟨i₀, hi₀, hsum ▸ sum_mem fun e he ↦ Submodule.smul_mem _ ⟨k e, ?_⟩ (subset_hull he)⟩
  have het := mem_of_mem_erase he
  simp only [k, sub_nonneg]
  by_cases hge : 0 < g e
  · rw [← le_div_iff₀ hge]
    exact w e (mem_filter.mpr ⟨het, hge⟩)
  · grw [not_lt.mp hge, mul_zero, ← fpos e]
    positivity [fpos i₀]

/-- **Carathéodory's theorem** for cones. -/
theorem hull_eq_union : (hull 𝕜 s : Set E) =
    ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : LinearIndepOn 𝕜 id (t : Set E)), hull 𝕜 (t : Set E) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨t, hts, hx⟩ : ∃ t : Finset E, ↑t ⊆ s ∧ x ∈ hull 𝕜 (t : Set E) := by
      obtain ⟨f, t, hts, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hx
      exact ⟨t, hts, sum_mem fun e he ↦ Submodule.smul_mem _ _ (subset_hull he)⟩
    simp only [mem_iUnion, exists_prop]
    induction t using Finset.strongInduction with | H t ih =>
    by_cases h : LinearIndepOn 𝕜 id (t : Set E)
    · exact ⟨t, hts, h, hx⟩
    obtain ⟨y, hy, hxy⟩ := mem_hull_erase h hx
    exact ih _ (erase_ssubset hy) (subset_trans (by simp) hts) hxy
  · iterate 3 convert Set.iUnion_subset _; intro
    exact Submodule.span_mono ‹_›

/-- A point in the conic hull of `s` can be represented as a positive span of linearly
independent vectors. A more explicit version of `hull_eq_union`. -/
theorem eq_pos_span_of_mem_hull (hx : x ∈ hull 𝕜 s) : ∃ (ι : Type u) (_ : Fintype ι),
    ∃ (z : ι → E) (w : ι → 𝕜),
      Set.range z ⊆ s ∧ LinearIndependent 𝕜 z ∧ (∀ i, 0 < w i) ∧ ∑ i, w i • z i = x := by
  rw [← SetLike.mem_coe, hull_eq_union] at hx
  simp only [exists_prop, Set.mem_iUnion] at hx
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  obtain ⟨w, -, hw₁, hw₂⟩ := mem_hull_finset.mp ht₃
  let t' := {i ∈ t | w i ≠ 0}
  refine ⟨t', t'.fintypeCoeSort, ((↑) : t' → E), fun i ↦ w i, ?_, ?_, ?_, ?_⟩
  · rw [Subtype.range_coe_subtype]
    exact Subset.trans (filter_subset _ t) ht₁
  · exact ht₂.mono (coe_subset.mpr (filter_subset _ t))
  · exact fun i ↦ (hw₁ i).lt_of_ne (mem_filter.mp i.2).2.symm
  · rw [sum_coe_sort t' fun e ↦ w e • e, sum_filter_of_ne, hw₂]
    intro e _ h contra
    apply h
    rw [contra, zero_smul]

end PointedCone
