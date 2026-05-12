/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Set
public import Mathlib.Order.Closure

/-!
# IsConvexSet hull

This file defines the convex hull of a set in a convex space. `convexHull R s` is the smallest
convex set containing `s`. In order theory speak, this is a closure operator.
-/

public section

open Set

namespace Convexity
variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y] {C s t : Set X} {x y : X}

variable (R) in
/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convexHull (s : Set X) : Set X :=
  ClosureOperator.ofCompletePred (IsConvexSet R) (fun _ ↦ .sInter) s

lemma subset_convexHull_iff : t ⊆ convexHull R s ↔ ∀ C, s ⊆ C → IsConvexSet R C → t ⊆ C := by
  simp [convexHull, iInter_subtype, iInter_and]

@[simp] lemma subset_convexHull_self : s ⊆ convexHull R s := ClosureOperator.le_closure _ s

protected lemma IsConvexSet.convexHull : IsConvexSet R (convexHull R s) :=
  ClosureOperator.isClosed_closure (.ofCompletePred (IsConvexSet R) _) s

lemma convexHull_eq_iInter :
    convexHull R s = ⋂ (t : Set X) (_ : s ⊆ t) (_ : IsConvexSet R t), t := by
  simp [convexHull, iInter_subtype, iInter_and]

lemma mem_convexHull_iff : x ∈ convexHull R s ↔ ∀ t, s ⊆ t → IsConvexSet R t → x ∈ t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]

lemma convexHull_min : s ⊆ C → IsConvexSet R C → convexHull R s ⊆ C :=
  (ClosureOperator.ofCompletePred (IsConvexSet R) _).closure_min

lemma IsConvexSet.convexHull_subset_iff (hC : IsConvexSet R C) : convexHull R s ⊆ C ↔ s ⊆ C :=
  ClosureOperator.IsClosed.closure_le_iff hC

@[gcongr]
lemma convexHull_mono (hst : s ⊆ t) : convexHull R s ⊆ convexHull R t :=
  ClosureOperator.monotone _ hst

lemma convexHull_eq_self : convexHull R C = C ↔ IsConvexSet R C :=
  (ClosureOperator.isClosed_iff _).symm

lemma convexHull_subset_self : convexHull R C ⊆ C ↔ IsConvexSet R C := by
  simp [← convexHull_eq_self, subset_antisymm_iff]

protected alias ⟨_, IsConvexSet.convexHull_eq_self⟩ := convexHull_eq_self

variable (R) in
@[simp] lemma convexHull_empty : convexHull R (∅ : Set X) = ∅ :=
  IsConvexSet.empty.convexHull_eq_self

@[simp] lemma convexHull_eq_empty : convexHull R s = ∅ ↔ s = ∅ := by
  simp [← subset_empty_iff, IsConvexSet.empty.convexHull_subset_iff]

@[simp] lemma convexHull_nonempty : (convexHull R s).Nonempty ↔ s.Nonempty := by
  simp [nonempty_iff_ne_empty]

protected alias ⟨_, Set.Nonempty.convexHull'⟩ := convexHull_nonempty

variable (R x) in
@[simp] lemma convexHull_singleton : convexHull R {x} = {x} :=
  IsConvexSet.singleton.convexHull_eq_self

@[simp] lemma convexHull_univ : convexHull R (univ : Set X) = univ :=
  IsConvexSet.univ.convexHull_eq_self

@[simp] lemma convexHull_eq_singleton : convexHull R s = {x} ↔ s = {x} where
  mp hs := by
    rw [← Set.Nonempty.subset_singleton_iff, ← hs]
    · exact subset_convexHull_self
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

variable (R s t) in
lemma convexHull_convexHull_union :
    convexHull R (convexHull R s ∪ t) = convexHull R (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left ..

variable (R s t) in
lemma convexHull_union_convexHull_right :
    convexHull R (s ∪ convexHull R t) = convexHull R (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right ..

lemma IsConvexSet.sdiff_singleton_iff_notMem_convexHull (hs : IsConvexSet R s) :
    IsConvexSet R (s \ {x}) ↔ x ∉ convexHull R (s \ {x}) where
  mp hsx hx := by
    rw [hsx.convexHull_eq_self] at hx
    exact hx.2 (mem_singleton _)
  mpr hx := by
    rw [← convexHull_subset_self]
    rintro y hy
    exact ⟨convexHull_min diff_subset hs hy, by rintro rfl; exact hx hy⟩

lemma IsAffineMap.image_convexHull {f : X → Y} (hf : IsAffineMap R f) (s : Set X) :
    f '' convexHull R s = convexHull R (f '' s) := by
  rw [subset_antisymm_iff,
    image_subset_iff, (IsConvexSet.convexHull.preimage hf).convexHull_subset_iff,
    ← image_subset_iff, (IsConvexSet.convexHull.image hf).convexHull_subset_iff]
  exact ⟨subset_convexHull_self, image_mono subset_convexHull_self⟩

namespace ConvexSet

variable {K K₁ K₂ : ConvexSet R X}

variable (R) in
def convexHull (s : Set X) : ConvexSet R X := ⟨Convexity.convexHull R s, .convexHull⟩

instance : Max (ConvexSet R X) where
  max K₁ K₂ := convexHull R (K₁ ∪ K₂)

lemma sup_eq_convexHull_union : (K₁ ⊔ K₂).carrier = Convexity.convexHull R (K₁ ∪ K₂) := by rfl

instance : SemilatticeSup (ConvexSet R X) where
  sup := max
  le_sup_left _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  le_sup_right _ _ _ hs := by
    apply subset_convexHull_self
    simp [hs]
  sup_le K₁ K₂ K₃ h₁₂ h₂₃ x hx := by
    rw [← mem_carrier, sup_eq_convexHull_union, mem_convexHull_iff] at hx
    refine hx K₃ ?_ K₃.isConvexSet
    simp [h₂₃, h₁₂]

instance : SupSet (ConvexSet R X) where
  sSup S := convexHull R (⋃ s ∈ S, s)

instance : CompleteSemilatticeSup (ConvexSet R X) where
  __ := instSemilatticeSup
  isLUB_sSup K := by
    constructor <;> intro L hL
    · intro l hl
      exact (subset_iUnion₂_of_subset _ hL fun ⦃_⦄ a ↦ a).trans subset_convexHull_self hl
    · simp only [sSup, convexHull, Convexity.convexHull, ClosureOperator.ofCompletePred_apply,
      le_eq_subset, iInf_eq_iInter]
      intro x xm
      simp only [← mem_carrier, mem_iInter, Subtype.forall, iUnion_subset_iff, and_imp] at xm
      exact xm _ hL L.isConvexSet

end Convexity.ConvexSet
