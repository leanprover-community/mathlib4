/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Polytope.Basic

/-! This file defines `Polytope`, the bundled version of `IsPolytope`. -/

public section

namespace Convexity

open ConvexSpace

variable {R X : Type*}

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable (R X) in
/-- A polytope is the convex hull of finitely many points. -/
structure Polytope where
  /-- The carrier of the polytope. -/
  carrier : Set X
  isPolytope : IsPolytope R carrier

end Semiring

namespace Polytope

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

instance : SetLike (Polytope R X) X where
  coe := Polytope.carrier
  coe_injective P₁ P₂ _ := by cases P₁; cases P₂; congr

variable {P P₁ P₂ : Polytope R X}

variable (P) in
@[simp] lemma carrier_eq_coe : P.carrier = P := rfl

@[ext] theorem ext (h : ∀ x, x ∈ P₁ ↔ x ∈ P₂) : P₁ = P₂ := SetLike.ext h

@[simp] theorem mem_mk {s h x} : x ∈ (⟨s, h⟩ : Polytope R X) ↔ x ∈ s := .rfl

@[simp] theorem mk_eq {s h} : (⟨s, h⟩ : Polytope R X) = s := by ext; simp

/- # LE -/

instance : PartialOrder (Polytope R X) := .ofSetLike ..

/- # Bot -/

instance : OrderBot (Polytope R X) where
  bot := ⟨∅, IsPolytope.empty R X⟩
  bot_le := fun _ _ => by simp

instance : Inhabited (Polytope R X) := ⟨⊥⟩

/- # Singleton -/

instance : Singleton X (Polytope R X) where
  singleton x := ⟨{x}, .singleton R x⟩

/- # Max -/

variable (R) in
/-- The convex hull of a `Finset s` as a `Polytope`. -/
def convexHull (s : Finset X) : Polytope R X :=
  ⟨_, IsPolytope.convexHull_finite R s.finite_toSet⟩

instance : Max (Polytope R X) where
  max P₁ P₂ := ⟨_, P₁.isPolytope.convexHull_union P₂.isPolytope⟩

lemma coe_sup_eq_convexHull_union :
  ((P₁ ⊔ P₂ : Polytope R X) : Set X) = Convexity.convexHull R (P₁ ∪ P₂) := rfl

instance : SemilatticeSup (Polytope R X) where
  sup := max
  le_sup_left _ _ := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    exact subset_trans Set.subset_union_left subset_convexHull_self
  le_sup_right _ _ := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    exact subset_trans Set.subset_union_right subset_convexHull_self
  sup_le a b c ha hb := by
    rw [← SetLike.coe_subset_coe, coe_sup_eq_convexHull_union]
    have : IsConvexSet R (c : Set X) := c.isPolytope.isConvexSet
    rw [← convexHull_eq_self.mpr this]
    apply convexHull_mono
    simp_all only [SetLike.coe_subset_coe, Set.union_subset_iff, and_self]

end Semiring

end Polytope

end Convexity
