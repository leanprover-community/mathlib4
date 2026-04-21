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

This file defines the notion of dually finitely generated cones. A cone is dually finitely
generated (or `DualFG` for short) if it is the dual of a finite set, or equivalently, of a
finitely generated cone. In geometric terms, a cone is dually finitely generated if it can
be written as the intersection of finitely many halfspaces. This is also known as an H-cone.
This is the counterpart to `FG` (finitely generated) which states that the cone is the conic hull
of a finite set, or a V-cone.

In finite dimensional vector spaces, `FG` is equivalent to `DualFG` by the Minkowski-Weyl theorem.
In this case, V- and H-cones are known as polyhedral cones.

## Main declarations

- `PointedCone.DualFG` expresses that a cone is the dual of a finite set.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace PointedCone

variable {R M N : Type*}
variable [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {p : M →ₗ[R] N →ₗ[R] R}

variable (p) in
/-- A cone is dually finitely generated (`DualFG`) if it is the dual of a finite set. Equivalently,
the cone can be written as the intersection of finitely many halfspace. It is also known as an
H-cone. This is the counterpart to `FG` (finitely generated) which states that the cone is the span
of a finite set, or a V-cone. -/
def DualFG (C : PointedCone R N) : Prop := ∃ s : Finset M, dual p s = C

/-- The top cone is dually finitely generated. -/
@[simp] protected lemma DualFG.top : DualFG p ⊤ := ⟨∅, by simp⟩

/-- A dually finitely generated cone is the dual of a finitely generated cone. -/
lemma DualFG.exists_fg_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := by
  obtain ⟨s, hs⟩ := hC; exact ⟨_, Submodule.fg_span s.finite_toSet, by simp [hs]⟩

/-- A cone is dually finitely generated if and only if it is the dual of a finitely generated
cone. -/
lemma DualFG.iff_exists_fg_dual {C : PointedCone R N} :
    C.DualFG p ↔ ∃ D : PointedCone R M, D.FG ∧ dual p D = C where
  mp h := h.exists_fg_dual
  mpr := by
    rintro ⟨_, ⟨s, rfl⟩, rfl⟩
    use s; simp

/-- A dually finitely generated cone is dually finitely generated w.r.t. the identity pairing. -/
lemma DualFG.id {C : PointedCone R N} (hC : C.DualFG p) : C.DualFG .id := by classical
  obtain ⟨s, rfl⟩ := hC
  use Finset.image p s
  simp

variable (p) in
/-- The dual of a finite set is dually finitely generated. -/
lemma DualFG.dual_of_finset (s : Finset M) : (dual p s).DualFG p := by use s

variable (p) in
/-- The dual of a finite set is dually finitely generated. -/
lemma DualFG.dual_of_finite {s : Set M} (hs : s.Finite) : (dual p s).DualFG p := by
  use hs.toFinset
  rw [Set.Finite.coe_toFinset]

variable (p) in
/-- The dual of a finitely generated cone is dually finitely generated. -/
lemma DualFG.dual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).DualFG p := by
  obtain ⟨s, rfl⟩ := hC
  use s; rw [← dual_hull]

alias FG.dual_dualfg := DualFG.dual_of_fg

/-- The intersection of two dually finitely generated cones is again dually finitely generated. -/
lemma DualFG.inf {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    (C ⊓ D).DualFG p := by classical
  obtain ⟨S, rfl⟩ := hC; obtain ⟨T, rfl⟩ := hD
  use S ∪ T; rw [Finset.coe_union, dual_union]

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, hDualFG, rfl⟩ := exists_fg_dual hC
  exact dual_dual_flip_dual (p := p) D

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
lemma DualFG.dual_flip_dual {C : PointedCone R M} (hC : C.DualFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

end PointedCone
