/-
Copyright (c) 2025 Yaël Dillies, Matthew Johnson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matthew Johnson
-/
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull

/-!
# Polytopes

We define polytopes as convex hulls of finite sets.
-/

open scoped Pointwise

variable {R 𝕜 E : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E] {s t : Set E} {x y : E}

variable (R) in
/-- A set is a polytope if it is the convex hull of finitely many points. -/
def IsPolytope (s : Set E) : Prop := ∃ t : Finset E, s = convexHull R t

@[simp] protected lemma IsPolytope.empty : IsPolytope R (∅ : Set E) := ⟨∅, by simp⟩
@[simp] protected lemma IsPolytope.singleton : IsPolytope R {x} := ⟨{x}, by simp⟩

@[simp] protected lemma IsPolytope.segment : IsPolytope R <| segment R x y := by
  classical exact ⟨{x, y}, by simp⟩

@[simp]
lemma IsPolytope.convexHull_finset {s : Finset E} : IsPolytope R <| convexHull R s.toSet := by use s

end Semiring

section Ring
variable [Ring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup E] [Module R E] {s t : Set E} {x y : E}

protected lemma IsPolytope.neg : IsPolytope R s → IsPolytope R (-s) := by
  classical rintro ⟨A, rfl⟩; exact ⟨-A, by simp [convexHull_neg]⟩

end Ring

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] {s t : Set E} {x y : E}

protected lemma IsPolytope.add : IsPolytope 𝕜 s → IsPolytope 𝕜 t → IsPolytope 𝕜 (s + t) := by
  classical rintro ⟨A, rfl⟩ ⟨B, rfl⟩; exact ⟨A + B, by simp [convexHull_add]⟩

protected lemma IsPolytope.sub (hs : IsPolytope 𝕜 s) (ht : IsPolytope 𝕜 t) :
    IsPolytope 𝕜 (s - t) := by simpa [sub_eq_add_neg] using hs.add ht.neg

end Field
