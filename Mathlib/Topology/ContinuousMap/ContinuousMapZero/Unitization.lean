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
`
## Main declarations

+ `ContinuousMap.toContinuousMapZero`: the retraction `C(X, R) → C(X, R)₀` given by `g ↦ g - g 0`
  of the coercion `C(X, R)₀ → C(X, R)`.
+ `ContinuousMapZero.unitizationStarAlgEquiv`: the star algebra isomorphism
  `Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R)`
-/

@[expose] public section

open ContinuousMapZero Unitization

namespace ContinuousMap

variable {X R : Type*} [TopologicalSpace X] [Zero X] [TopologicalSpace R]
variable [AddCommGroup R] [IsTopologicalAddGroup R]

/-- This is the canonical retraction of the coercion `C(X, R)₀ → C(X, R)` given by
`fun g x ↦ g x - g 0`. -/
def toContinuousMapZero (g : C(X, R)) : C(X, R)₀ where
  toContinuousMap := g - const X (g 0)
  map_zero' := by simp

@[simp]
lemma toContinuousMapZero_apply (g : C(X, R)) (x : X) : g.toContinuousMapZero x = g x - g 0 := rfl

@[simp]
lemma coe_toContinuousMapZero (g : C(X, R)) :
    (g.toContinuousMapZero : C(X, R)) = g - const X (g 0) :=
  rfl

@[simp]
lemma toContinuousMapZero_const (r : R) : (const X r).toContinuousMapZero = 0 := by ext; simp

@[simp]
lemma toContinuousMapZero_zero : (0 : C(X, R)).toContinuousMapZero = 0 := by ext; simp

@[simp]
lemma toContinuousMapZero_coe (f : C(X, R)₀) : (f : C(X, R)).toContinuousMapZero = f := by
  ext; simp

lemma toContinuousMapZero_surjective :
    Function.Surjective (toContinuousMapZero (X := X) (R := R)) :=
  fun f ↦ ⟨f, toContinuousMapZero_coe f⟩

@[fun_prop]
lemma continuous_toContinuousMapZero :
    Continuous (toContinuousMapZero : C(X, R) → C(X, R)₀) := by
  rw [ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff]
  exact continuous_id.sub <| continuous_const'.comp <| continuous_eval_const 0

end ContinuousMap

namespace ContinuousMapZero

variable {X R : Type*} [TopologicalSpace X] [Zero X] [TopologicalSpace R]
variable [CommRing R] [IsTopologicalRing R] [StarRing R] [ContinuousStar R]

variable (X R) in
/-- The canonical star algebra isomorphism `Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R)` which sends
`(r, f)` to function `fun x ↦ r + f x` whose inverse sends `g` to `(g 0, fun x ↦ g x - g 0)`.

This is the map obtained by lifting the coercion `C(X, R)₀ → C(X, R)` to the unitization
(see `ContinuousMapZero.toStarAlgHom_unitizationStarAlgEquiv`). -/
def unitizationStarAlgEquiv : Unitization R C(X, R)₀ ≃⋆ₐ[R] C(X, R) where
  toFun := starLift (toContinuousMapHom (X := X) (R := R))
  invFun g := .mk (g 0, g.toContinuousMapZero)
  left_inv f := Unitization.ext (by simp [starLift_apply, ← StarAlgHom.coe_toAlgHom])
    (by ext x; simp [starLift_apply, ← StarAlgHom.coe_toAlgHom])
  right_inv g := by ext x; simp [starLift_apply, ← StarAlgHom.coe_toAlgHom]
  map_add' := map_add _
  map_mul' := map_mul _
  map_smul' := map_smul _
  map_star' := map_star _

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

lemma unitizationStarAlgEquiv_symm_apply (g : C(X, R)) :
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
