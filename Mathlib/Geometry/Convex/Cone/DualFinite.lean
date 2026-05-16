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
def DualFG (C : PointedCone R N) : Prop := ∃ D : PointedCone R M, D.FG ∧ dual p D = C

/-- The top cone is dually finitely generated. -/
@[simp] protected lemma DualFG.top : DualFG p ⊤ := ⟨⊥, by simp [Submodule.fg_bot]⟩

/-- A dually finitely generated cone is the dual of a finitely generated cone. -/
@[deprecated "This is the definition of PointedCone.DualFG" (since := "2026-04-10")]
lemma DualFG.exists_fg_dual {C : PointedCone R N} (hC : C.DualFG p) :
    ∃ D : PointedCone R M, D.FG ∧ dual p D = C := hC

/-- A cone is dually finitely generated if and only if it is the dual of a finitely generated
cone. -/
@[deprecated "This is the definition of PointedCone.DualFG" (since := "2026-04-10")]
lemma DualFG.iff_exists_fg_dual {C : PointedCone R N} :
    C.DualFG p ↔ ∃ D : PointedCone R M, D.FG ∧ dual p D = C := .rfl

/-- A dually finitely generated cone is dually finitely generated w.r.t. the identity pairing. -/
lemma DualFG.id {C : PointedCone R N} (hC : C.DualFG p) : C.DualFG .id := by
  obtain ⟨D, hfg, rfl⟩ := hC
  use D.map p
  simpa using hfg.map _

variable (p) in
/-- The dual of a finitely generated cone is dually finitely generated. -/
lemma DualFG.dual_of_fg {C : PointedCone R M} (hC : C.FG) : (dual p C).DualFG p := by use C

variable (p) in
/-- The dual of a finite set is dually finitely generated. -/
@[deprecated "Use `DualFG.dual_of_fg` and `Submodule.fg_span`" (since := "2026-04-10")]
lemma DualFG.dual_of_finset (s : Finset M) : (dual p (hull R s)).DualFG p := by
  use hull R s
  simp [Submodule.fg_span]

variable (p) in
/-- The dual of a finite set is dually finitely generated. -/
@[deprecated "Use `DualFG.dual_of_fg` and `Submodule.fg_span`" (since := "2026-04-10")]
lemma DualFG.dual_of_finite {s : Set M} (hs : s.Finite) : (dual p (hull R s)).DualFG p := by
  use hull R s
  simp [Submodule.fg_span hs]

alias FG.dual_dualfg := DualFG.dual_of_fg

/-- The intersection of two dually finitely generated cones is again dually finitely generated. -/
lemma DualFG.inf {C D : PointedCone R N} (hC : C.DualFG p) (hD : D.DualFG p) :
    (C ⊓ D).DualFG p := by
  obtain ⟨C', hfgC, rfl⟩ := hC
  obtain ⟨D', hfgD, rfl⟩ := hD
  exact ⟨C' ⊔ D', hfgC.sup hfgD, dual_sup C' D'⟩

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
lemma DualFG.dual_dual_flip {C : PointedCone R N} (hC : C.DualFG p) :
    dual p (dual p.flip C) = C := by
  obtain ⟨D, -, rfl⟩ := hC
  exact dual_dual_flip_dual D

/-- The double dual of a dually finitely generated cone is the cone itself. -/
@[simp]
lemma DualFG.dual_flip_dual {C : PointedCone R M} (hC : C.DualFG p.flip) :
    dual p.flip (dual p C) = C := hC.dual_dual_flip

end PointedCone
