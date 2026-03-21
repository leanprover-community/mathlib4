/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Duals of finitely generated cones

This files defines the notion `FGDual` for cones that can be written as the dual of a finite set,
or equivalently, that are duals of finitely generated cones. In geometric terms, a cone is
FGDual if it can be written as the intersection of finitely many halfspaces. This is the counterpart
to FG (finitely generated) which states that the cone is the span of a finite set.

In finite dimensional vector spaces, FG is equivalent to FGDual by the Minkowski-Weyl theorem.

## Main declarations

- `PointedCone.FGDual` expresses that a cone is the dual of a finite set.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is `FGDual` if it is the dual of a finite set. Equivalently, the cone can be written
  as the intersection of finitely many halfspace. This is the counterpart to `FG` (finitely
  generated) which states that the cone is the span of a finite set. -/
def FGDual (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

/-- The top cone is FGDual. -/
lemma FGDual.top : FGDual p ⊤ := ⟨∅, by simp⟩

/-- An FGDual cone is the dual of an FG cone. -/
lemma FGDual.exists_fg_dual {C : PointedCone R N} (hC : C.FGDual p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- An FGDual cone is FGDual w.r.t. the identity pairing. -/
lemma FGDual.to_fgdual_id {C : PointedCone R N} (hC : C.FGDual p) : C.FGDual .id := by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

variable (p) in
/-- The dual of a finite set is FGDual. -/
lemma FGDual.of_dual_finset (s : Finset M) : (dual p s).FGDual p := by use s

variable (p) in
/-- The dual of an FG cone is FGDual. -/
lemma FGDual.of_dual_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).FGDual p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_span]

alias FG.dual_fgdual := FGDual.of_dual_fg

/-- The intersection of two FGDual cones is FGDual. -/
lemma FGDual.inf {C D : PointedCone R N} (hC : C.FGDual p) (hD : D.FGDual p) :
    (C ⊓ D).FGDual p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of an FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_dual_flip {C : PointedCone R N} (hC : C.FGDual p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hfgdual, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of an FGDual cone is the cone itself. -/
@[simp]
lemma FGDual.dual_flip_dual {C : PointedCone R M} (hC : C.FGDual p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

end PointedCone
