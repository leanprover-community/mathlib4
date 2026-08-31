/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.Geometry.Convex.ConvexSpace.AffineSpace
public import Mathlib.Geometry.Convex.Hull
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar

/-!
This file introduces convex polytopes as V-polytopes and proves basic facts.

## Main declarations

* `IsPolytope`: states that a set is the convex hull of finitely many points.
-/

public noncomputable section

namespace Convexity

variable {R X Y V A : Type*}

open ConvexSpace

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable (R) in
/-- A set is a polytope if it is the convex hull of finitely many points. This is the V-polytope
definition for convex polytope. -/
def IsPolytope (s : Set X) : Prop := ∃ t : Finset X, s = convexHull R t

end Semiring

namespace IsPolytope

section Semiring

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [ConvexSpace R X]

variable {P P₁ P₂ : Set X}

lemma isConvexSet (hP : IsPolytope R P) : IsConvexSet R P := by
  obtain ⟨_, rfl⟩ := hP
  exact .convexHull

variable (R X) in
@[simp] protected lemma empty : IsPolytope R (∅ : Set X) := by
  use ∅; simp

variable (R) in
@[simp] protected lemma singleton (x : X) : IsPolytope R {x} := by
  use {x}; simp

variable (R) in
lemma of_subsingleton (hP : P.Subsingleton) : IsPolytope R P := by
  obtain rfl | ⟨x, rfl⟩ := hP.eq_empty_or_singleton <;> simp

variable (R) in
lemma convexHull_of_finite {v : Set X} (hv : v.Finite) :
    IsPolytope R (convexHull R v) := by use hv.toFinset; simp

lemma convexHull_union (h₁ : IsPolytope R P₁) (h₂ : IsPolytope R P₂) :
    IsPolytope R (convexHull R (P₁ ∪ P₂)) := by classical
  obtain ⟨v₁, rfl⟩ := h₁
  obtain ⟨v₂, rfl⟩ := h₂
  use v₁ ∪ v₂
  simp [convexHull_union_convexHull, convexHull_convexHull_union]

lemma convexHull_sUnion_of_finite {p : Set (Set X)} (hp : p.Finite)
    (h : ∀ P ∈ p, IsPolytope R P) : IsPolytope R (convexHull R (⋃₀ p)) := by
  induction p, hp using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ h' =>
    rw [Set.sUnion_insert, ← convexHull_union_convexHull]
    simp only [Set.mem_insert_iff, forall_eq_or_imp] at h
    exact convexHull_union h.1 (h' h.2)

variable [ConvexSpace R Y] {f : X → Y}

protected lemma image (hf : IsAffineMap R f) (hP : IsPolytope R P) :
    IsPolytope R (f '' P) := by classical
  obtain ⟨v, rfl⟩ := hP
  use v.image f
  simpa using hf.image_convexHull v

end Semiring

end IsPolytope

end Convexity
