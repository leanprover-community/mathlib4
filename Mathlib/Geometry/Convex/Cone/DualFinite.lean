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

This files defines the notion of dually finitely generated cones. A cone is dually finitely
generated (or `DualFG` for short) if it is the dual of a finite set, or equivalently, of a
finitely generated cone. In geometric terms, a cone is DualFG if it can be written as the
intersection of finitely many halfspaces. This is the counterpart to FG (finitely generated)
which states that the cone is the span of a finite set.

In finite dimensional vector spaces, FG is equivalent to DualFG by the Minkowski-Weyl theorem.

## Main declarations

- `PointedCone.DualFG` expresses that a cone is the dual of a finite set.

-/

@[expose] public section

namespace PointedCone

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is dually finitely generated (`DualFG`) if it is the dual of a finite set. Equivalently,
  the cone can be written as the intersection of finitely many halfspace. This is the counterpart
  to `FG` (finitely generated) which states that the cone is the span of a finite set. -/
def DualFG (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

/-- The top cone is DualFG. -/
lemma DualFG.top : DualFG p ⊤ := ⟨∅, by simp⟩

/-- An DualFG cone is the dual of an FG cone. -/
lemma DualFG.exists_fg_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- An DualFG cone is DualFG w.r.t. the identity pairing. -/
lemma DualFG.to_dualfg_id {C : PointedCone R N} (hC : C.DualFG p) : C.DualFG .id := by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

variable (p) in
/-- The dual of a finite set is DualFG. -/
lemma DualFG.of_dual_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/-- The dual of an FG cone is DualFG. -/
lemma DualFG.dual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).DualFG p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_span]

alias FG.dual_dualfg := DualFG.dual_of_fg

/-- The intersection of two DualFG cones is DualFG. -/
lemma DualFG.inf {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    (C ⊓ D).DualFG p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of an DualFG cone is the cone itself. -/
@[simp]
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of an DualFG cone is the cone itself. -/
@[simp]
lemma DualFG.dual_flip_dual {C : PointedCone R M} (hC : C.DualFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

end PointedCone
