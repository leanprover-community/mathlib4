/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Strict

/-!

# Induced bicategories

In this file we develop API for constructing a full sub-bicategory of a bicategory.

## TODO

One might also want to develop "locally induced" bicategories, which should allow for a sub-class
of 1-morphisms as well. However, this needs more thought. If tries the naive approach of simply
replacing the map `F` below with a "functor" (between `CategoryStruct`s), one runs into the issue
that `map_comp` and `map_id` might not be definitional equalities (which they should be in
practice). Hence one needs to carefully carry these around, or specify `F` in a way that ensures
they are def-eqs, perhaps constructing it from specified `MorhpismProperty`s.
-/

namespace CategoryTheory.Bicategory

variable {B : Type*} (C : Type*) [Bicategory C] (F : B → C)

/-- `InducedBicategory B C`, where `F : B → C`, is a hardened type alias for `B`. This is given
a bicategory structure where the 1-morphisms `X ⟶ Y` are the 1-morphisms in `C` from `F X` to
`F Y`, and the 2-morphisms `f ⟶ g` are also the 2-morphisms in `C` from `f` to `g`.
-/
@[nolint unusedArguments]
structure InducedBicategory (_F : B → C) where
  /-- Interpret an element of `B` as an element of `InducedBicategory`. -/
  of ::
  /-- The element of `B` underlying an element of `InducedBicategory`. -/
  as : B

namespace InducedBicategory

variable {C F}

instance hasCoeToSort {α : Sort*} [CoeSort C α] : CoeSort (InducedBicategory C F) α :=
  ⟨fun c => F c.as⟩

/-- `InducedBicategory.Hom X Y` is the type of morphisms between `X` and `Y` viewed as objects of
the bicategory `B`. This is given a `CategoryStruct` instance below, where the identity and
composition is induced from `C`. -/
structure Hom (X Y : InducedBicategory C F) where
  /-- Construct a morphism in `InducedBicategory C F` from a morhism in `C`. -/
  mkHom ::
  /-- The morphism in `C` underlying the morphism in `InducedBicategory C F`. -/
  hom : F X.as ⟶ F Y.as

@[simps id_hom comp_hom]
instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X.as)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[simps!]
instance Hom.category (X Y : InducedBicategory C F) : Category (X ⟶ Y) where
  Hom f g := f.hom ⟶ g.hom
  id X := 𝟙 _
  comp u v := u ≫ v

/-- Constructor for 2-isomorphisms in the induced bicategory. -/
@[simps!]
def isoMk {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom) : f ≅ g where
  hom := φ.hom
  inv := φ.inv

@[simps!]
instance bicategory : Bicategory (InducedBicategory C F) where
  __ := categoryStruct
  whiskerLeft {_ _ _} h {_ _} η := h.hom ◁ η
  whiskerRight {_ _ _} {_ _} η h := η ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (λ_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange := whisker_exchange

attribute [-simp] bicategory_comp_hom bicategory_Hom

section

/-- The forgetful pseudofunctor from an induced bicategory to the original bicategory,
forgetting the extra data.
-/
@[simps!]
def inducedPseudofunctor : StrictPseudofunctor (InducedBicategory C F) C :=
  StrictPseudofunctor.mk' {
    obj X := F X.as
    map f := f.hom
    map₂ η := η }

end

end InducedBicategory

end CategoryTheory.Bicategory
