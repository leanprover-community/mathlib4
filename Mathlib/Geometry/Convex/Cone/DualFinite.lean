
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Geometry.Convex.Cone.Dual

import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Cardinal.Defs

namespace PointedCone

open Module Function

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

/-- An FGDual cone is FGDual w.r.t. the standard pairing. -/
lemma FGDual.to_id {C : PointedCone R N} (hC : C.FGDual p) : C.FGDual .id := by classical
  obtain ⟨s, hs⟩ := hC
  use Finset.image p s
  simp [← dual_id, hs]

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
