/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Kim Morrison
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Preliminary design for Jacobians in algebraic geometry

We use `theorem_wanted` / `def_wanted` to describe the types and universal characterisations
we want to see completed in Mathlib.

This is based on Christian Merten's `JacobianChallenge.lean`
(https://github.com/leanprover/lean-eval/blob/main/LeanEval/AlgebraicGeometry/JacobianChallenge.lean).

Every dependency between "wanted" declarations is expressed via the `❰…❱` bracket syntax, so the
recorded placeholder types carry the full dependency graph.

By a smooth curve we mean a geometrically irreducible, smooth scheme of relative dimension one
over a field.
-/

-- Every declaration here is an intentionally private `def_wanted` / `theorem_wanted` /
-- `instance_wanted` placeholder, so the module exports nothing.
set_option linter.privateModule false

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  [SmoothOfRelativeDimension 1 C.hom]
  [IsProper C.hom]
  [GeometricallyIrreducible C.hom]

/-- The genus of a smooth proper curve. -/
def_wanted genus (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ

/-- The Jacobian of a smooth, proper curve over a field `k`. -/
def_wanted Jacobian (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    Over (Spec (.of k))

namespace Jacobian

/-! ## The Jacobian of `C` is an abelian variety. -/

/-- The group scheme structure on the Jacobian of the curve `C`. -/
instance_wanted : GrpObj (❰Jacobian❱ C)

/-- The Jacobian of `C` is smooth of relative dimension `g` over `k`, where `g` is the
genus of `C`. -/
instance_wanted : SmoothOfRelativeDimension (❰genus❱ C) (❰Jacobian❱ C).hom

/-- The Jacobian of `C` is proper over `k`. -/
instance_wanted : IsProper (❰Jacobian❱ C).hom

/-- The Jacobian of `C` is geometrically irreducible over `k`. -/
instance_wanted : GeometricallyIrreducible (❰Jacobian❱ C).hom

/-- The Abel-Jacobi map from a smooth, proper curve to its Jacobian associated to a
`k`-rational point of `C`. -/
def_wanted ofCurve (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    C ⟶ ❰Jacobian❱ C

/-- The Abel-Jacobi map sends the `k`-rational point `P` to `0`, where `0` (denoted by `η` below)
is the neutral element of the group scheme `Jacobian C`. -/
theorem_wanted comp_ofCurve (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    P ≫ ❰ofCurve❱ P = η[❰Jacobian❱ C]

/-- The universal property of the Jacobian variety: for any abelian variety `A`, any morphism
`f : C ⟶ A` such that `f(P) = 0` factors uniquely through the Jacobian of `C`. In other words,
`Jacobian C` is the Albanese variety of `C`. -/
theorem_wanted exists_unique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : ❰Jacobian❱ C ⟶ A), f = ❰ofCurve❱ P ≫ g

end Jacobian

end AlgebraicGeometry
