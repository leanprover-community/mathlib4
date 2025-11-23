/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Points of a site

Let `C` be a category equipped with a Grothendieck topology `J`. In this file,
we define the notion of point of the site `(C, J)`, as a
structure `GrothendieckTopology.Point`. Such a `Φ : J.Point` consists
in a functor `Φ.fiber : C ⥤ Type w` such that the category `Φ.fiber.Elements`
is cofiltered (and initially small) and such that if `x : Φ.fiber.obj X`
and `R` is a covering sieve of `X`, then `x` belongs to the image
of some `y : Φ.fiber.obj Y` by a morphism `f : Y ⟶ X` which belongs to `R`.
(This definition is essentially the definition of a fiber functor on a site
from SGA 4 IV 6.3.)

The fact that `Φ.fiber.Elementsᵒᵖ` is filtered allows to define
`Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` by taking the filtering colimit
of the evaluation functors at `op X` when `(X : C, x : F.obj X)` varies in
`Φ.fiber.Elementsᵒᵖ`. We define `Φ.sheafFiber : Sheaf J A ⥤ A` as the
restriction of `Φ.presheafFiber` to the full subcategory of sheaves.

-/

@[expose] public section

universe w' w v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- Given `J` a Grothendieck topology on a category `C`, a point of the site `(C, J)`
consists of a functor `fiber : C ⥤ Type w` such that the category `fiber.Elements`
is initally small (which allows defining the fiber functor on presheaves by
taking colimits) and cofiltered (so that the fiber functor on presheaves is exact),
and such that covering sieves induce jointly surjective maps on fibers (which
allows to show that the fibers of a presheaf and its associated sheaf are isomorphic). -/
structure Point where
  /-- the fiber functor on the underlying category of the site -/
  fiber : C ⥤ Type w
  isCofiltered : IsCofiltered fiber.Elements := by infer_instance
  initiallySmall : InitiallySmall.{w} fiber.Elements := by infer_instance
  jointly_surjective {X : C} (R : Sieve X) (h : R ∈ J X) (x : fiber.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x

namespace Point

attribute [instance] initiallySmall isCofiltered

variable {J} (Φ : Point.{w} J) {A : Type u'} [Category.{v'} A]
  [HasColimitsOfSize.{w, w} A]

instance : HasColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _

instance [LocallySmall.{w} C] [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    HasExactColimitsOfShape Φ.fiber.Elementsᵒᵖ A :=
  hasExactColimitsOfShape_of_final _
    (FinallySmall.fromFilteredFinalModel Φ.fiber.Elementsᵒᵖ)

/-- The fiber functor on categories of presheaves that is given by a point of a site. -/
noncomputable def presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π Φ.fiber).op ⋙ colim

/-- The fiber functor on the category of sheaves that is given a by a point of a site. -/
noncomputable abbrev sheafFiber : Sheaf J A ⥤ A :=
  sheafToPresheaf J A ⋙ Φ.presheafFiber

end Point

end GrothendieckTopology

end CategoryTheory
