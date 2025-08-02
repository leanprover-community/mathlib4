/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Elementwise
import Mathlib.Topology.Sequences
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Category.TopCat.Basic
/-!

# The category of sequential topological spaces

We define the category `Sequential` of sequential topological spaces. We follow the usual template
for defining categories of topological spaces, by giving it the induced category structure from
`TopCat`.
-/

open CategoryTheory

universe u

/-- The type sequential topological spaces. -/
structure Sequential where
  /-- The underlying topological space of an object of `Sequential`. -/
  toTop : TopCat.{u} -- TODO: turn this into `extends`
  /-- The underlying topological space is sequential. -/
  [is_sequential : SequentialSpace toTop]

namespace Sequential

instance : Inhabited Sequential.{u} :=
  ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

instance : CoeSort Sequential Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_sequential

instance : Category.{u, u+1} Sequential.{u} :=
  InducedCategory.category toTop

instance : ConcreteCategory.{u} Sequential.{u} (C(·, ·)) :=
  InducedCategory.concreteCategory toTop

variable (X : Type u) [TopologicalSpace X] [SequentialSpace X]

/-- Constructor for objects of the category `Sequential`. -/
abbrev of : Sequential.{u} where
  toTop := TopCat.of X
  is_sequential := ‹_›

/-- The fully faithful embedding of `Sequential` in `TopCat`. -/
@[simps!]
def sequentialToTop : Sequential.{u} ⥤ TopCat.{u} :=
  inducedFunctor _

/-- The functor to `TopCat` is indeed fully faithful. -/
def fullyFaithfulSequentialToTop : sequentialToTop.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : sequentialToTop.{u}.Full  :=
  inferInstanceAs (inducedFunctor _).Full

instance : sequentialToTop.{u}.Faithful :=
  inferInstanceAs (inducedFunctor _).Faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : Sequential.{u}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := TopCat.ofHom ⟨f, f.continuous⟩
  inv := TopCat.ofHom ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : Sequential.{u}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.continuous
  continuous_invFun := f.inv.hom.continuous

/-- The equivalence between isomorphisms in `Sequential` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : Sequential.{u}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

end Sequential
