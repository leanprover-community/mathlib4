/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Topology.Sheaves.Presheaf
/-!
# Presheaves of functions

We construct some simple examples of presheaves of functions on a topological space.
* `presheafToTypes X T`, where `T : X → Type`,
  is the presheaf of dependently-typed (not-necessarily continuous) functions
* `presheafToType X T`, where `T : Type`,
  is the presheaf of (not-necessarily-continuous) functions to a fixed target type `T`
* `presheafToTop X T`, where `T : TopCat`,
  is the presheaf of continuous functions into a topological space `T`
* `presheafToTopCommRing X R`, where `R : TopCommRingCat`
  is the presheaf valued in `CommRing` of functions into a topological ring `R`
* as an example of the previous construction,
  `presheafToTopCommRing X (TopCommRingCat.of ℂ)`
  is the presheaf of rings of continuous complex-valued functions on `X`.
-/

open CategoryTheory TopologicalSpace Opposite

namespace TopCat

variable (X : TopCat)

/-- The presheaf of dependently typed functions on `X`, with fibres given by a type family `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToTypes (T : X → Type*) : X.Presheaf (Type _) where
  obj U := ∀ x : U.unop, T x
  map {_ V} i g := fun x : V.unop => g (i.unop x)
  map_id U := by
    ext g
    rfl
  map_comp {_ _ _} _ _ := rfl

@[simp]
theorem presheafToTypes_obj {T : X → Type*} {U : (Opens X)ᵒᵖ} :
    (presheafToTypes X T).obj U = ∀ x : U.unop, T x :=
  rfl

@[simp]
theorem presheafToTypes_map {T : X → Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToTypes X T).map i f = fun x => f (i.unop x) :=
  rfl

-- We don't just define this in terms of `presheafToTypes`,
-- as it's helpful later to see (at a syntactic level) that `(presheafToType X T).obj U`
-- is a non-dependent function.
-- We don't use `@[simps]` to generate the projection lemmas here,
-- as it turns out to be useful to have `presheafToType_map`
-- written as an equality of functions (rather than being applied to some argument).
/-- The presheaf of functions on `X` with values in a type `T`.
There is no requirement that the functions are continuous, here.
-/
def presheafToType (T : Type*) : X.Presheaf (Type _) where
  obj U := U.unop → T
  map {_ _} i g := g ∘ i.unop
  map_id U := by
    ext g
    rfl
  map_comp {_ _ _} _ _ := rfl

@[simp]
theorem presheafToType_obj {T : Type*} {U : (Opens X)ᵒᵖ} :
    (presheafToType X T).obj U = (U.unop → T) :=
  rfl

@[simp]
theorem presheafToType_map {T : Type*} {U V : (Opens X)ᵒᵖ} {i : U ⟶ V} {f} :
    (presheafToType X T).map i f = f ∘ i.unop :=
  rfl

/-- The presheaf of continuous functions on `X` with values in fixed target topological space
`T`. -/
def presheafToTop (T : TopCat) : X.Presheaf (Type _) :=
  (Opens.toTopCat X).op ⋙ yoneda.obj T

@[simp]
theorem presheafToTop_obj (T : TopCat) (U : (Opens X)ᵒᵖ) :
    (presheafToTop X T).obj U = ((Opens.toTopCat X).obj (unop U) ⟶ T) :=
  rfl

end TopCat
