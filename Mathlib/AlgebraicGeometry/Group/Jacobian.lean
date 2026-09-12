/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Kim Morrison
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

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

## Curves without rational points

The Jacobian `Jacobian C` and its structure as an abelian variety are defined for every smooth
proper curve `C`, whether or not `C` has a `k`-rational point. Only the Abel-Jacobi map
`Jacobian.ofCurve` and the universal property `Jacobian.existsUnique_ofCurve_comp` depend on the
choice of a rational point `P`, and say nothing when `C` has no rational point. Base change
(`Jacobian.baseChange`) fills most of this gap: a smooth geometrically irreducible curve acquires
a rational point after a finite separable extension `K / k`, and the universal property of
`Jacobian (C_K) ≅ (Jacobian C)_K` then characterises the base change of `Jacobian C` to `K`.
Pinning down `Jacobian C` itself also needs the Galois descent datum, or a point-free universal
property phrased via the Albanese torsor `Pic¹`; neither is recorded in this blueprint yet.
-/

-- Every declaration here is either an intentionally private `def_wanted` / `theorem_wanted` /
-- `instance_wanted` placeholder, or a private helper instance needed to state one, so the
-- module exports nothing.
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

/-- The group structure on the Jacobian of `C` is commutative, so `Jacobian C` is an abelian
variety. Given the instances below, this is a consequence of
`isCommMonObj_of_isProper_of_geometricallyIntegral`, as soon as Mathlib knows that a smooth
geometrically irreducible scheme over a field is geometrically integral. -/
instance_wanted : IsCommMonObj (❰Jacobian❱ C)

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
theorem_wanted existsUnique_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∃! (g : ❰Jacobian❱ C ⟶ A), f = ❰ofCurve❱ P ≫ g

/-- Any factorisation through the Abel-Jacobi map as in `existsUnique_ofCurve_comp` is
automatically a homomorphism of group schemes: such a `g` preserves the neutral element
(precompose with `P` and use `comp_ofCurve`), so this is a special case of rigidity
(`isMonHom_of_one_comp` below). -/
theorem_wanted isMonHom_of_ofCurve_comp (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C)
    {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom] [GrpObj A]
    [GeometricallyIrreducible A.hom] (f : C ⟶ A) (hf : P ≫ f = η[A]) :
    ∀ g : ❰Jacobian❱ C ⟶ A, f = ❰ofCurve❱ P ≫ g → IsMonHom g

/-! ## Base change

For a field extension `K / k`, viewed as a morphism `f : Spec K ⟶ Spec k`, the base change of
`Jacobian C` along `f` is the Jacobian of the base change of `C`, compatibly with the group
structures and with the Abel-Jacobi maps. Base change along `f` is the functor
`Over.pullback f : Over (Spec k) ⥤ Over (Spec K)`. -/

section BaseChange

open scoped CategoryTheory.Obj

variable {K : Type u} [Field K] (f : Spec (.of K) ⟶ Spec (.of k))

-- Instance search does not see through `(Over.pullback f).obj X` to the underlying
-- `pullback.snd X.hom f`, so we record the base change instances we need here.

instance (X : Over (Spec (.of k))) [IsProper X.hom] : IsProper ((Over.pullback f).obj X).hom := by
  dsimp; infer_instance

instance (X : Over (Spec (.of k))) (n : ℕ) [SmoothOfRelativeDimension n X.hom] :
    SmoothOfRelativeDimension n ((Over.pullback f).obj X).hom := by
  dsimp; infer_instance

instance (X : Over (Spec (.of k))) [GeometricallyIrreducible X.hom] :
    GeometricallyIrreducible ((Over.pullback f).obj X).hom := by
  dsimp; infer_instance

/-- The genus of a smooth proper curve is invariant under base change. -/
theorem_wanted genus_baseChange (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    ❰genus❱ ((Over.pullback f).obj C) = ❰genus❱ C

/-- The Jacobian commutes with base change: the base change along `f : Spec K ⟶ Spec k` of the
Jacobian of `C` is the Jacobian of the base change of `C`. -/
def_wanted baseChange (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    (Over.pullback f).obj (❰Jacobian❱ C) ≅ ❰Jacobian❱ ((Over.pullback f).obj C)

/-- The base change isomorphism `Jacobian.baseChange` is an isomorphism of group schemes over
`K`, where the base change of `Jacobian C` carries the group structure inherited from
`Jacobian C` (via `CategoryTheory.Functor.grpObjObj`). -/
-- This can be an `instance_wanted` after
-- https://github.com/leanprover-community/batteries/pull/1959 is merged.
theorem_wanted isMonHom_baseChange_hom (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] :
    IsMonHom (❰baseChange❱ f C).hom

/-- The Abel-Jacobi map is compatible with base change: the base change of `ofCurve P`,
composed with `Jacobian.baseChange`, is the Abel-Jacobi map of the base-changed curve at the
base-changed point `P`. -/
theorem_wanted ofCurve_baseChange (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : 𝟙_ (Over (Spec (.of k))) ⟶ C) :
    (Over.pullback f).map (❰ofCurve❱ P) ≫ (❰baseChange❱ f C).hom =
      ❰ofCurve❱ (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map P)

end BaseChange

end Jacobian

/-! ## Rigidity

Rigidity is the reason `Jacobian.existsUnique_ofCurve_comp` above quantifies over plain
morphisms rather than homomorphisms of group schemes: by
`Jacobian.isMonHom_of_ofCurve_comp`, any `g` satisfying `f = ofCurve P ≫ g` is
automatically a homomorphism, so uniqueness among all morphisms is the stronger statement.
-/

/-- Rigidity: a morphism from an abelian variety over `k` to a group scheme over `k` that
sends the neutral element to the neutral element is automatically a homomorphism of group
schemes. Note only the source needs to be an abelian variety. -/
theorem_wanted isMonHom_of_one_comp {A B : Over (Spec (.of k))}
    [Smooth A.hom] [IsProper A.hom] [GrpObj A] [GeometricallyIrreducible A.hom]
    [GrpObj B] (f : A ⟶ B) (hf : η[A] ≫ f = η[B]) : IsMonHom f

end AlgebraicGeometry
