/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.FieldSimp

#align_import analysis.convex.caratheodory from "leanprover-community/mathlib"@"e6fab1dc073396d45da082c644642c4f8bff2264"

/-!
# Carathéodory's convexity theorem

Convex hull can be regarded as a refinement of affine span. Both are closure operators but whereas
convex hull takes values in the lattice of convex subsets, affine span takes values in the much
coarser sublattice of affine subspaces.

The cost of this refinement is that one no longer has bases. However Carathéodory's convexity
theorem offers some compensation. Given a set `s` together with a point `x` in its convex hull,
Carathéodory says that one may find an affine-independent family of elements `s` whose convex hull
contains `x`. Thus the difference from the case of affine span is that the affine-independent family
depends on `x`.

In particular, in finite dimensions Carathéodory's theorem implies that the convex hull of a set `s`
in `𝕜ᵈ` is the union of the convex hulls of the `(d + 1)`-tuples in `s`.

## Main results

* `convexHull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/


open Set Finset

open BigOperators

universe u

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Caratheodory

/-- If `x` is in the convex hull of some finset `t` whose elements are not affine-independent,
then it is in the convex hull of a strict subset of `t`. -/
theorem mem_convexHull_erase [DecidableEq E] {t : Finset E} (h : ¬AffineIndependent 𝕜 ((↑) : t → E))
    {x : E} (m : x ∈ convexHull 𝕜 (↑t : Set E)) :
    ∃ y : (↑t : Set E), x ∈ convexHull 𝕜 (↑(t.erase y) : Set E) := by
  simp only [Finset.convexHull_eq, mem_setOf_eq] at m ⊢
  -- ⊢ ∃ y w x_1 x_2, centerMass (erase t ↑y) w id = x
  obtain ⟨f, fpos, fsum, rfl⟩ := m
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  obtain ⟨g, gcombo, gsum, gpos⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  clear h
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  let s := @Finset.filter _ (fun z => 0 < g z) (fun _ => LinearOrder.decidableLT _ _) t
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  obtain ⟨i₀, mem, w⟩ : ∃ i₀ ∈ s, ∀ i ∈ s, f i₀ / g i₀ ≤ f i / g i := by
    apply s.exists_min_image fun z => f z / g z
    obtain ⟨x, hx, hgx⟩ : ∃ x ∈ t, 0 < g x := gpos
    exact ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩
  have hg : 0 < g i₀ := by
    rw [mem_filter] at mem
    exact mem.2
  have hi₀ : i₀ ∈ t := filter_subset _ _ mem
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  let k : E → 𝕜 := fun z => f z - f i₀ / g i₀ * g z
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  have hk : k i₀ = 0 := by field_simp [ne_of_gt hg]
  -- ⊢ ∃ y w x x, centerMass (erase t ↑y) w id = centerMass t f id
  have ksum : ∑ e in t.erase i₀, k e = 1 := by
    calc
      ∑ e in t.erase i₀, k e = ∑ e in t, k e := by
        conv_rhs => rw [← insert_erase hi₀, sum_insert (not_mem_erase i₀ t), hk, zero_add]
      _ = ∑ e in t, (f e - f i₀ / g i₀ * g e) := rfl
      _ = 1 := by rw [sum_sub_distrib, fsum, ← mul_sum, gsum, mul_zero, sub_zero]
  refine' ⟨⟨i₀, hi₀⟩, k, _, by convert ksum, _⟩
  -- ⊢ ∀ (y : E), y ∈ erase t ↑{ val := i₀, property := hi₀ } → 0 ≤ k y
  · simp only [and_imp, sub_nonneg, mem_erase, Ne.def, Subtype.coe_mk]
    -- ⊢ ∀ (y : E), ¬y = i₀ → y ∈ t → f i₀ / g i₀ * g y ≤ f y
    intro e _ het
    -- ⊢ f i₀ / g i₀ * g e ≤ f e
    by_cases hes : e ∈ s
    -- ⊢ f i₀ / g i₀ * g e ≤ f e
    · have hge : 0 < g e := by
        rw [mem_filter] at hes
        exact hes.2
      rw [← le_div_iff hge]
      -- ⊢ f i₀ / g i₀ ≤ f e / g e
      exact w _ hes
      -- 🎉 no goals
    · calc
        _ ≤ 0 := by
          apply mul_nonpos_of_nonneg_of_nonpos
          · apply div_nonneg (fpos i₀ (mem_of_subset (filter_subset _ t) mem)) (le_of_lt hg)
          · simpa only [mem_filter, het, true_and_iff, not_lt] using hes
        _ ≤ f e := fpos e het
  · rw [Subtype.coe_mk, centerMass_eq_of_sum_1 _ id ksum]
    -- ⊢ ∑ i in erase t i₀, k i • id i = centerMass t f id
    calc
      ∑ e in t.erase i₀, k e • e = ∑ e in t, k e • e := sum_erase _ (by rw [hk, zero_smul])
      _ = ∑ e in t, (f e - f i₀ / g i₀ * g e) • e := rfl
      _ = t.centerMass f id := by
        simp only [sub_smul, mul_smul, sum_sub_distrib, ← smul_sum, gcombo, smul_zero, sub_zero,
          centerMass, fsum, inv_one, one_smul, id.def]
#align caratheodory.mem_convex_hull_erase Caratheodory.mem_convexHull_erase

variable {s : Set E} {x : E} (hx : x ∈ convexHull 𝕜 s)

/-- Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum
cardinality, whose convex hull contains `x`. -/
noncomputable def minCardFinsetOfMemConvexHull : Finset E :=
  Function.argminOn Finset.card Nat.lt_wfRel.2 { t | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } <| by
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, exists_prop, mem_iUnion] using hx
    -- 🎉 no goals
#align caratheodory.min_card_finset_of_mem_convex_hull Caratheodory.minCardFinsetOfMemConvexHull

theorem minCardFinsetOfMemConvexHull_subseteq : ↑(minCardFinsetOfMemConvexHull hx) ⊆ s :=
  (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).1
#align caratheodory.min_card_finset_of_mem_convex_hull_subseteq Caratheodory.minCardFinsetOfMemConvexHull_subseteq

theorem mem_minCardFinsetOfMemConvexHull :
    x ∈ convexHull 𝕜 (minCardFinsetOfMemConvexHull hx : Set E) :=
  (Function.argminOn_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).2
#align caratheodory.mem_min_card_finset_of_mem_convex_hull Caratheodory.mem_minCardFinsetOfMemConvexHull

theorem minCardFinsetOfMemConvexHull_nonempty : (minCardFinsetOfMemConvexHull hx).Nonempty := by
  rw [← Finset.coe_nonempty, ← @convexHull_nonempty_iff 𝕜]
  -- ⊢ Set.Nonempty (↑(convexHull 𝕜) ↑(minCardFinsetOfMemConvexHull hx))
  exact ⟨x, mem_minCardFinsetOfMemConvexHull hx⟩
  -- 🎉 no goals
#align caratheodory.min_card_finset_of_mem_convex_hull_nonempty Caratheodory.minCardFinsetOfMemConvexHull_nonempty

theorem minCardFinsetOfMemConvexHull_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ convexHull 𝕜 (t : Set E)) : (minCardFinsetOfMemConvexHull hx).card ≤ t.card :=
  Function.argminOn_le _ _ _ (by exact ⟨ht₁, ht₂⟩)
                                 -- 🎉 no goals
#align caratheodory.min_card_finset_of_mem_convex_hull_card_le_card Caratheodory.minCardFinsetOfMemConvexHull_card_le_card

theorem affineIndependent_minCardFinsetOfMemConvexHull :
    AffineIndependent 𝕜 ((↑) : minCardFinsetOfMemConvexHull hx → E) := by
  let k := (minCardFinsetOfMemConvexHull hx).card - 1
  -- ⊢ AffineIndependent 𝕜 Subtype.val
  have hk : (minCardFinsetOfMemConvexHull hx).card = k + 1 :=
    (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (minCardFinsetOfMemConvexHull_nonempty hx))).symm
  classical
  by_contra h
  obtain ⟨p, hp⟩ := mem_convexHull_erase h (mem_minCardFinsetOfMemConvexHull hx)
  have contra := minCardFinsetOfMemConvexHull_card_le_card hx (Set.Subset.trans
    (Finset.erase_subset (p : E) (minCardFinsetOfMemConvexHull hx))
    (minCardFinsetOfMemConvexHull_subseteq hx)) hp
  rw [← not_lt] at contra
  apply contra
  erw [card_erase_of_mem p.2, hk]
  exact lt_add_one _
#align caratheodory.affine_independent_min_card_finset_of_mem_convex_hull Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull

end Caratheodory

variable {s : Set E}

/-- **Carathéodory's convexity theorem** -/
theorem convexHull_eq_union : convexHull 𝕜 s =
    ⋃ (t : Finset E) (hss : ↑t ⊆ s) (hai : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t := by
  apply Set.Subset.antisymm
  -- ⊢ ↑(convexHull 𝕜) s ⊆ ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 S …
  · intro x hx
    -- ⊢ x ∈ ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 Subtype.val), ↑(c …
    simp only [exists_prop, Set.mem_iUnion]
    -- ⊢ ∃ i, ↑i ⊆ s ∧ AffineIndependent 𝕜 Subtype.val ∧ x ∈ ↑(convexHull 𝕜) ↑i
    exact ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
      Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx,
      Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx,
      Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  · iterate 3 convert Set.iUnion_subset _; intro
    -- ⊢ ↑(convexHull 𝕜) ↑i✝² ⊆ ↑(convexHull 𝕜) s
    exact convexHull_mono ‹_›
    -- 🎉 no goals
#align convex_hull_eq_union convexHull_eq_union

/-- A more explicit version of `convexHull_eq_union`. -/
theorem eq_pos_convex_span_of_mem_convexHull {x : E} (hx : x ∈ convexHull 𝕜 s) :
    ∃ (ι : Sort (u + 1)) (_ : Fintype ι),
      ∃ (z : ι → E) (w : ι → 𝕜) (_ : Set.range z ⊆ s) (_ : AffineIndependent 𝕜 z)
        (_ : ∀ i, 0 < w i), ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  rw [convexHull_eq_union] at hx
  -- ⊢ ∃ ι x_1 z w x_2 x_3 x_4, ∑ i : ι, w i = 1 ∧ ∑ i : ι, w i • z i = x
  simp only [exists_prop, Set.mem_iUnion] at hx
  -- ⊢ ∃ ι x_1 z w x_2 x_3 x_4, ∑ i : ι, w i = 1 ∧ ∑ i : ι, w i • z i = x
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx
  -- ⊢ ∃ ι x_1 z w x_2 x_3 x_4, ∑ i : ι, w i = 1 ∧ ∑ i : ι, w i • z i = x
  simp only [t.convexHull_eq, exists_prop, Set.mem_setOf_eq] at ht₃
  -- ⊢ ∃ ι x_1 z w x_2 x_3 x_4, ∑ i : ι, w i = 1 ∧ ∑ i : ι, w i • z i = x
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃
  -- ⊢ ∃ ι x_1 z w x_2 x_3 x_4, ∑ i : ι, w i = 1 ∧ ∑ i : ι, w i • z i = x
  let t' := t.filter fun i => w i ≠ 0
  -- ⊢ ∃ ι x_1 z w x_2 x_3 x_4, ∑ i : ι, w i = 1 ∧ ∑ i : ι, w i • z i = x
  refine' ⟨t', t'.fintypeCoeSort, ((↑) : t' → E), w ∘ ((↑) : t' → E), _, _, _, _, _⟩
  · rw [Subtype.range_coe_subtype]
    -- ⊢ {x | x ∈ t'} ⊆ s
    exact Subset.trans (Finset.filter_subset _ t) ht₁
    -- 🎉 no goals
  · exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i ≠ 0) t)⟩
    -- 🎉 no goals
  · exact fun i =>
      (hw₁ _ (Finset.mem_filter.mp i.2).1).lt_of_ne (Finset.mem_filter.mp i.property).2.symm
  · erw [Finset.sum_attach, Finset.sum_filter_ne_zero, hw₂]
    -- 🎉 no goals
  · change (∑ i : t' in t'.attach, (fun e => w e • e) ↑i) = x
    -- ⊢ ∑ i in attach t', (fun e => w e • e) ↑i = x
    erw [Finset.sum_attach (f := fun e => w e • e), Finset.sum_filter_of_ne]
    -- ⊢ ∑ x in t, w x • x = x
    · rw [t.centerMass_eq_of_sum_1 id hw₂] at hw₃
      -- ⊢ ∑ x in t, w x • x = x
      exact hw₃
      -- 🎉 no goals
    · intro e _ hwe contra
      -- ⊢ False
      apply hwe
      -- ⊢ w e • e = 0
      rw [contra, zero_smul]
      -- 🎉 no goals
#align eq_pos_convex_span_of_mem_convex_hull eq_pos_convex_span_of_mem_convexHull
