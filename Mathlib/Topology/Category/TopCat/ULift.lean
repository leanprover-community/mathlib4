/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Lifting topological spaces to a higher universe

In this file, we construct the functor `uliftFunctor.{v, u} : TopCat.{u} ⥤ TopCat.{max u v}`
which sends a topological space `X : Type u` to a homeomorphic space in `Type (max u v)`.

-/

universe v u

open CategoryTheory

namespace TopCat

-- Note: no `@[simps!]` attribute here in order to get good simplification lemmas
-- like `uliftFunctorObjHomeo_naturality_apply` below. We should access
-- `uliftFunctor.obj X` via the homeomorphism `X.uliftFunctorObjHomeo`.
/-- The functor which sends a topological space in `Type u` to a homeomorphic
space in `Type (max u v)`. -/
def uliftFunctor : TopCat.{u} ⥤ TopCat.{max u v} where
  obj X := TopCat.of (ULift.{v} X)
  map {X Y} f := ofHom ⟨ULift.map f, by continuity⟩

/-- Given `X : TopCat.{u}`, this is the homeomorphism `X ≃ₜ uliftFunctor.{v}.obj X`. -/
def uliftFunctorObjHomeo (X : TopCat.{u}) : X ≃ₜ uliftFunctor.{v}.obj X :=
  Homeomorph.ulift.symm

@[simp]
lemma uliftFunctorObjHomeo_naturality_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    uliftFunctor.{v}.map f (X.uliftFunctorObjHomeo x) =
      Y.uliftFunctorObjHomeo (f x) := rfl

@[simp]
lemma uliftFunctorObjHomeo_symm_naturality_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : uliftFunctor.{v}.obj X) :
    Y.uliftFunctorObjHomeo.symm (uliftFunctor.{v}.map f x) =
      f (X.uliftFunctorObjHomeo.symm x) :=
  rfl

/-- The `ULift` functor on categories of topological spaces is compatible
with the one defined on categories of types. -/
@[simps!]
def uliftFunctorCompForgetIso : uliftFunctor.{v, u} ⋙ forget TopCat.{max u v} ≅
    forget TopCat.{u} ⋙ CategoryTheory.uliftFunctor.{v, u} := Iso.refl _

/-- The `ULift` functor on categories of topological spaces is fully faithful. -/
def uliftFunctorFullyFaithful : uliftFunctor.{v, u}.FullyFaithful where
  preimage f := ofHom ⟨ULift.down ∘ f ∘ ULift.up, by continuity⟩

instance : uliftFunctor.{v, u}.Full :=
  uliftFunctorFullyFaithful.full

instance : uliftFunctor.{v, u}.Faithful :=
  uliftFunctorFullyFaithful.faithful

end TopCat
