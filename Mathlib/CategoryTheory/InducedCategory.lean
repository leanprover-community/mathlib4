/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!
# Induced categories and full subcategories

Given a category `D` and a function `F : C → D` from a type `C` to the
objects of `D`, there is an essentially unique way to give `C` a
category structure such that `F` becomes a fully faithful functor,
namely by taking $ Hom_C(X, Y) = Hom_D(FX, FY) $. We call this the
category induced from `D` along `F`.

## Implementation notes

The type of morphisms between `X` and `Y` in `InducedCategory D F` is
not definitionally equal to `F X ⟶ F Y`. Instead, this type is made
a `1`-field structure. Use `InducedCategory.homMk` to construct
morphisms in induced categories.

-/

@[expose] public section


namespace CategoryTheory

universe v v₂ u₁ u₂
-- morphism levels before object levels. See note [category theory universes].

section Induced

variable {C : Type u₁} (D : Type u₂) [Category.{v} D]
variable (F : C → D)

/-- `InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint unusedArguments]
def InducedCategory (_F : C → D) : Type u₁ :=
  C

variable {D}

namespace InducedCategory

instance hasCoeToSort {α : Sort*} [CoeSort D α] :
    CoeSort (InducedCategory D F) α :=
  ⟨fun c => F c⟩

variable {F}

/-- The type of morphisms in `InducedCategory D F` between `X` and `Y`
is a 1-field structure which identifies to `F X ⟶ F Y`. -/
@[ext]
structure Hom (X Y : InducedCategory D F) where
  /-- The underlying morphism. -/
  hom : F X ⟶ F Y

@[simps id_hom comp_hom]
instance : Category.{v} (InducedCategory D F) where
  Hom X Y := Hom X Y
  id X := { hom := 𝟙 _ }
  comp f g := { hom := f.hom ≫ g.hom }

attribute [reassoc] comp_hom

@[ext]
lemma hom_ext {X Y : InducedCategory D F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- Construct a morphism in the induced category
from a morphism in the original category. -/
@[simps] def homMk {X Y : InducedCategory D F} (f : F X ⟶ F Y) : X ⟶ Y where
  hom := f

/-- Morphisms in `InducedCategory D F` identify to morphisms in `D`. -/
@[simps!]
def homEquiv {X Y : InducedCategory D F} : (X ⟶ Y) ≃ (F X ⟶ F Y) where
  toFun f := f.hom
  invFun f := homMk f

/-- Construct an isomorphism in the induced category
from an isomorphism in the original category. -/
@[simps] def isoMk {X Y : InducedCategory D F} (f : F X ≅ F Y) : X ≅ Y where
  hom := homMk f.hom
  inv := homMk f.inv

end InducedCategory

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedFunctor : InducedCategory D F ⥤ D where
  obj := F
  map f := f.hom

/-- The induced functor `inducedFunctor F : InducedCategory D F ⥤ D` is fully faithful. -/
def fullyFaithfulInducedFunctor : (inducedFunctor F).FullyFaithful where
  preimage f := InducedCategory.homMk f

instance InducedCategory.full : (inducedFunctor F).Full :=
  (fullyFaithfulInducedFunctor F).full

instance InducedCategory.faithful : (inducedFunctor F).Faithful :=
  (fullyFaithfulInducedFunctor F).faithful

end Induced

end CategoryTheory
