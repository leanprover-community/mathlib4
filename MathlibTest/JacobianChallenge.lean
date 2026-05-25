/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Kim Morrison
-/
import Mathlib
import Batteries.Util.ProofWanted

/-!
# Jacobians in algebraic geometry, expressed via `proof_wanted` / `construction_wanted`

Christian Merten's `JacobianChallenge.lean`
(https://github.com/leanprover/lean-eval/blob/main/LeanEval/AlgebraicGeometry/JacobianChallenge.lean)
demonstrating Batteries' `construction_wanted` / `proof_wanted` infrastructure
(https://github.com/leanprover-community/batteries/pull/1818).

Every dependency between "wanted" declarations is expressed via the `❰…❱` bracket syntax, so the
recorded placeholder types carry the full dependency graph.

By a smooth curve we mean a geometrically irreducible, smooth scheme of relative dimension one
over a field.
-/

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.JacobianChallenge

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom]
  [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The genus of a smooth proper curve. -/
construction_wanted genus (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ

/-- The Jacobian of a smooth, proper curve over a field `k`. -/
construction_wanted Jacobian (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Over (Spec (.of k))

namespace Jacobian

/-! ## The Jacobian of `C` is an abelian variety. -/

/-- The group scheme structure on the Jacobian of the curve `C`. -/
instance_wanted instGrpObj : GrpObj (❰Jacobian❱ C)

/-- The Jacobian of `C` is smooth of relative dimension `g` over `k`, where `g` is the
genus of `C`. -/
instance_wanted smoothOfRelativeDimension_genus :
    SmoothOfRelativeDimension (❰genus❱ C) (❰Jacobian❱ C).hom

/-- The Jacobian of `C` is proper over `k`. -/
instance_wanted instIsProper : IsProper (❰Jacobian❱ C).hom

/-- The Jacobian of `C` is geometrically irreducible over `k`. -/
instance_wanted instGeometricallyIrreducible : GeometricallyIrreducible (❰Jacobian❱ C).hom

/-- The Abel-Jacobi map from a smooth, proper curve to its Jacobian associated to a
`k`-rational point of `C`. -/
construction_wanted ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    C ⟶ ❰Jacobian❱ C

/-- The Abel-Jacobi map sends the `k`-rational point `P` to `0`, where `0` (denoted by `η` below)
is the neutral element of the group scheme `Jacobian C`. -/
proof_wanted comp_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ❰ofCurve❱ P = η[❰Jacobian❱ C]

/-- The universal property of the Jacobian variety: for any abelian variety `A`, any morphism
`f : C ⟶ A` such that `f(P) = 0` factors uniquely through the Jacobian of `C`. In other words,
`Jacobian C` is the Albanese variety of `C`. -/
proof_wanted exists_unique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : ❰Jacobian❱ C ⟶ A), f = ❰ofCurve❱ P ≫ g

end Jacobian

end AlgebraicGeometry.JacobianChallenge
