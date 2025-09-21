/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convexHull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convexHull` is defined as a closure operator. This gives access to the `ClosureOperator` API
while the impact on writing code is minimal as `convexHull 𝕜 s` is automatically elaborated as
`(convexHull 𝕜) s`.
-/


open Set

open Pointwise

variable {𝕜 E F : Type*}

section convexHull

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable (𝕜)
variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
@[simps! isClosed]
def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ ↦ convex_sInter

variable (s : Set E)

theorem subset_convexHull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s

theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) := (convexHull 𝕜).isClosed_closure s

theorem convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : Convex 𝕜 t), t := by
  simp [convexHull, iInter_subtype, iInter_and]

variable {𝕜 s} {t : Set E} {x y : E}

theorem mem_convexHull_iff : x ∈ convexHull 𝕜 s ↔ ∀ t, s ⊆ t → Convex 𝕜 t → x ∈ t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]

theorem convexHull_min : s ⊆ t → Convex 𝕜 t → convexHull 𝕜 s ⊆ t := (convexHull 𝕜).closure_min

theorem Convex.convexHull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  (show (convexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
theorem convexHull_mono (hst : s ⊆ t) : convexHull 𝕜 s ⊆ convexHull 𝕜 t :=
  (convexHull 𝕜).monotone hst

lemma convexHull_eq_self : convexHull 𝕜 s = s ↔ Convex 𝕜 s := (convexHull 𝕜).isClosed_iff.symm

alias ⟨_, Convex.convexHull_eq⟩ := convexHull_eq_self

@[simp]
theorem convexHull_univ : convexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull 𝕜)

@[simp]
theorem convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅ :=
  convex_empty.convexHull_eq

@[simp]
theorem convexHull_eq_empty : convexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_convexHull 𝕜 _
  · rintro rfl
    exact convexHull_empty

@[deprecated (since := "2025-08-09")] alias convexHull_empty_iff := convexHull_eq_empty

@[simp]
theorem convexHull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne, Ne]
  exact not_congr convexHull_eq_empty

protected alias ⟨_, Set.Nonempty.convexHull⟩ := convexHull_nonempty_iff

theorem segment_subset_convexHull (hx : x ∈ s) (hy : y ∈ s) : segment 𝕜 x y ⊆ convexHull 𝕜 s :=
  (convex_convexHull _ _).segment_subset (subset_convexHull _ _ hx) (subset_convexHull _ _ hy)

@[simp]
theorem convexHull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x} :=
  (convex_singleton x).convexHull_eq

@[simp] lemma convexHull_eq_singleton : convexHull 𝕜 s = {x} ↔ s = {x} where
  mp hs := by
    rw [← Set.Nonempty.subset_singleton_iff, ← hs]
    · exact subset_convexHull ..
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

@[simp]
theorem convexHull_zero : convexHull 𝕜 (0 : Set E) = 0 :=
  convexHull_singleton 0

@[simp] lemma convexHull_eq_zero : convexHull 𝕜 s = 0 ↔ s = 0 := convexHull_eq_singleton

@[simp]
theorem convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHull 𝕜 {x, y} = segment 𝕜 x y := by
  refine (convexHull_min ?_ <| convex_segment _ _).antisymm
    (segment_subset_convexHull (mem_insert _ _) <| subset_insert _ _ <| mem_singleton _)
  rw [insert_subset_iff, singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩

theorem convexHull_convexHull_union_left (s t : Set E) :
    convexHull 𝕜 (convexHull 𝕜 s ∪ t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left _ _ _

theorem convexHull_convexHull_union_right (s t : Set E) :
    convexHull 𝕜 (s ∪ convexHull 𝕜 t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right _ _ _

theorem Convex.convex_remove_iff_notMem_convexHull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) :
    Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x}) := by
  constructor
  · rintro hsx hx
    rw [hsx.convexHull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}) by
    rw [h]
    exact convex_convexHull 𝕜 _
  exact
    Subset.antisymm (subset_convexHull 𝕜 _) fun y hy =>
      ⟨convexHull_min diff_subset hs hy, by
        rintro (rfl : y = x)
        exact hx hy⟩

@[deprecated (since := "2025-05-23")]
alias Convex.convex_remove_iff_not_mem_convexHull_remove :=
  Convex.convex_remove_iff_notMem_convexHull_remove

theorem IsLinearMap.image_convexHull {f : E → F} (hf : IsLinearMap 𝕜 f) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  Set.Subset.antisymm
    (image_subset_iff.2 <|
      convexHull_min (image_subset_iff.1 <| subset_convexHull 𝕜 _)
        ((convex_convexHull 𝕜 _).is_linear_preimage hf))
    (convexHull_min (image_mono (subset_convexHull 𝕜 s)) <|
      (convex_convexHull 𝕜 s).is_linear_image hf)

theorem LinearMap.image_convexHull (f : E →ₗ[𝕜] F) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  f.isLinear.image_convexHull s

theorem convexHull_add_subset {s t : Set E} :
    convexHull 𝕜 (s + t) ⊆ convexHull 𝕜 s + convexHull 𝕜 t :=
  convexHull_min (add_subset_add (subset_convexHull _ _) (subset_convexHull _ _))
    (Convex.add (convex_convexHull 𝕜 s) (convex_convexHull 𝕜 t))

end AddCommMonoid

end OrderedSemiring

section CommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

theorem convexHull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHull 𝕜 s :=
  (LinearMap.lsmul _ _ a).image_convexHull _ |>.symm

end CommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

theorem AffineMap.image_convexHull (f : E →ᵃ[𝕜] F) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) := by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine convexHull_min ?_ ((convex_convexHull 𝕜 (f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convexHull 𝕜 (f '' s)
  · exact convexHull_min (Set.image_mono (subset_convexHull 𝕜 s))
      ((convex_convexHull 𝕜 s).affine_image f)

theorem convexHull_subset_affineSpan (s : Set E) : convexHull 𝕜 s ⊆ (affineSpan 𝕜 s : Set E) :=
  convexHull_min (subset_affineSpan 𝕜 s) (affineSpan 𝕜 s).convex

@[simp]
theorem affineSpan_convexHull (s : Set E) : affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s := by
  refine le_antisymm ?_ (affineSpan_mono 𝕜 (subset_convexHull 𝕜 s))
  rw [affineSpan_le]
  exact convexHull_subset_affineSpan s

theorem convexHull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s := by
  simp_rw [← image_neg_eq_neg]
  exact AffineMap.image_convexHull (-1) _ |>.symm

lemma convexHull_vadd (x : E) (s : Set E) : convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexHull 𝕜 s :=
  (AffineEquiv.constVAdd 𝕜 _ x).toAffineMap.image_convexHull s |>.symm

end AddCommGroup

end OrderedRing

end convexHull
