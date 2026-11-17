/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero

/-!
# `C(X, R)` is the unitization of `C(X, R)₀`

The obvious non-unital star algebra homomorphism `C(X, R)₀ → C(X, R)` lifts to a map
`fun (r, f) x ↦ r + f x : Unitization R C(X, R)₀ → C(X, R)`. This map is a star algebra isomorphism
with inverse given by `fun f ↦ (f 0, fun x ↦ f x - f 0)`.

## Main declarations

+ `ContinuousMapZero.unitizationStarAlgEquiv`: the star algebra isomorphism
  `Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R)`
-/

@[expose] public section

open ContinuousMapZero Unitization

namespace ContinuousMapZero

variable {X R : Type*} [TopologicalSpace X] [Zero X] [TopologicalSpace R]
variable [CommRing R] [IsTopologicalRing R] [StarRing R] [ContinuousStar R]

variable (X R) in
/-- The canonical star algebra isomorphism `Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R)` which sends
`(r, f)` to the function `fun x ↦ r + f x` whose inverse sends `g` to `(g 0, fun x ↦ g x - g 0)`.

This is the map obtained by lifting the coercion `C(X, R)₀ → C(X, R)` to the unitization
(see `ContinuousMapZero.toStarAlgHom_unitizationStarAlgEquiv`). -/
def unitizationStarAlgEquiv : Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R) where
  __ := starLift (toContinuousMapHom (X := X) (R := R))
  toFun := starLift _
  invFun g := .mk (g 0, g.toContinuousMapZero)
  left_inv f := by ext <;> simp
  right_inv g := by ext; simp
  map_smul' := map_smul _

/-- `ContinuousMapZero.unitizationStarAlgEquiv` is the map obtained by lifting the coercion
`C(X, R)₀ → C(X, R)` to the unitization. -/
lemma toStarAlgHom_unitizationStarAlgEquiv :
    (unitizationStarAlgEquiv X R).toStarAlgHom =
      starLift (toContinuousMapHom (X := X) (R := R)) :=
  rfl

@[simp]
lemma unitizationStarAlgEquiv_apply_apply (f : Unitization R C(X, R)₀) (x : X) :
    unitizationStarAlgEquiv X R f x = f.fst + f.snd x :=
  rfl

lemma unitizationStarAlgEquiv_apply (f : Unitization R C(X, R)₀) :
    unitizationStarAlgEquiv X R f = .const X f.fst + f.snd := by
  ext; simp

lemma symm_unitizationStarAlgEquiv_apply (g : C(X, R)) :
    (unitizationStarAlgEquiv X R).symm g = .mk (g 0, g.toContinuousMapZero) :=
  rfl

@[simp]
lemma fst_symm_unitizationStarAlgEquiv (g : C(X, R)) :
    ((unitizationStarAlgEquiv X R).symm g).fst = g 0 :=
  rfl

@[simp]
lemma snd_symm_unitizationStarAlgEquiv (g : C(X, R)) :
    ((unitizationStarAlgEquiv X R).symm g).snd = g.toContinuousMapZero :=
  rfl

@[simp]
lemma unitizationStarAlgEquiv_inl (r : R) :
    unitizationStarAlgEquiv X R (inl r) = .const X r := by
  ext; simp

@[simp]
lemma unitizationStarAlgEquiv_inr (f : C(X, R)₀) : unitizationStarAlgEquiv X R f = f := by
  ext; simp

end ContinuousMapZero
