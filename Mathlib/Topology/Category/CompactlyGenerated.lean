/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.CategoryTheory.Elementwise
/-!
# Compactly generated topological spaces

This file defines the category of compactly generated topological spaces. These are spaces `X` such
that a map `f : X → Y` is continuous whenever the composition `S → X → Y` is continuous for all
compact Hausdorff spaces `S` mapping continuously to `X`.

## TODO

* `CompactlyGenerated` is a reflective subcategory of `TopCat`.
* `CompactlyGenerated` is Cartesian closed.
* Every first-countable space is `u`-compactly generated for every universe `u`.
-/

@[expose] public section

universe u w

open CategoryTheory Topology TopologicalSpace

/-- `CompactlyGenerated.{u, w}` is the type of `u`-compactly generated `w`-small topological spaces.
This should always be used with explicit universe parameters. -/
structure CompactlyGenerated where
  /-- The underlying topological space of an object of `CompactlyGenerated`. -/
  toTop : TopCat.{w}
  /-- The underlying topological space is compactly generated. -/
  [is_compactly_generated : UCompactlyGeneratedSpace.{u} toTop]

namespace CompactlyGenerated

instance : Inhabited CompactlyGenerated.{u, w} :=
  ⟨{ toTop := TopCat.of (ULift (Fin 37)) }⟩

instance : CoeSort CompactlyGenerated Type* :=
  ⟨fun X => X.toTop⟩

attribute [instance] is_compactly_generated

instance : Category.{w, w + 1} CompactlyGenerated.{u, w} :=
  inferInstanceAs <| Category (InducedCategory _ toTop)

instance : ConcreteCategory.{w} CompactlyGenerated.{u, w} (C(·, ·)) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toTop) _

variable (X : Type w) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]

/-- Constructor for objects of the category `CompactlyGenerated`. -/
abbrev of : CompactlyGenerated.{u, w} where
  toTop := TopCat.of X
  is_compactly_generated := ‹_›

section

variable {X} {Y : Type w} [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} Y]

/-- Typecheck a `ContinuousMap` as a morphism in `CompactlyGenerated`. -/
abbrev ofHom (f : C(X, Y)) : of X ⟶ of Y := ConcreteCategory.ofHom f

end

/-- The fully faithful embedding of `CompactlyGenerated` in `TopCat`. -/
@[simps!]
def compactlyGeneratedToTop : CompactlyGenerated.{u, w} ⥤ TopCat.{w} :=
  inducedFunctor _

/-- `compactlyGeneratedToTop` is fully faithful. -/
def fullyFaithfulCompactlyGeneratedToTop : compactlyGeneratedToTop.{u, w}.FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : compactlyGeneratedToTop.{u, w}.Full := fullyFaithfulCompactlyGeneratedToTop.full

instance : compactlyGeneratedToTop.{u, w}.Faithful := fullyFaithfulCompactlyGeneratedToTop.faithful

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv]
def isoOfHomeo {X Y : CompactlyGenerated.{u, w}} (f : X ≃ₜ Y) : X ≅ Y where
  hom := ofHom ⟨f, f.continuous⟩
  inv := ofHom ⟨f.symm, f.symm.continuous⟩
  hom_inv_id := by
    ext x
    exact f.symm_apply_apply x
  inv_hom_id := by
    ext x
    exact f.apply_symm_apply x

/-- Construct a homeomorphism from an isomorphism. -/
@[simps]
def homeoOfIso {X Y : CompactlyGenerated.{u, w}} (f : X ≅ Y) : X ≃ₜ Y where
  toFun := f.hom
  invFun := f.inv
  left_inv := f.hom_inv_id_apply
  right_inv := f.inv_hom_id_apply
  continuous_toFun := f.hom.hom.hom.continuous
  continuous_invFun := f.inv.hom.hom.continuous

/-- The equivalence between isomorphisms in `CompactlyGenerated` and homeomorphisms
of topological spaces. -/
@[simps]
def isoEquivHomeo {X Y : CompactlyGenerated.{u, w}} : (X ≅ Y) ≃ (X ≃ₜ Y) where
  toFun := homeoOfIso
  invFun := isoOfHomeo

end CompactlyGenerated
