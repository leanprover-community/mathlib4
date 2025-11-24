/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

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

@[expose] public section

namespace CategoryTheory.Bicategory

variable {B : Type*} (C : Type*) [Bicategory C] (F : B → C)

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`. This is given
a bicategory structure where the 1-morphisms `X ⟶ Y` are the 1-morphisms in `C` from `F X` to
`F Y`, and the 2-morphisms `f ⟶ g` are also the 2-morphisms in `C` from `f` to `g`.
-/
@[nolint unusedArguments]
def InducedBicategory (_F : B → C) :=
  B

namespace InducedBicategory

variable {C F}

instance hasCoeToSort {α : Sort*} [CoeSort C α] : CoeSort (InducedBicategory C F) α :=
  ⟨fun c => F c⟩

/-- `InducedBicategory.Hom X Y` is the type of morphisms between `X` and `Y` viewed as objects of
the bicategory `B`. This is given a `CategoryStruct` instance below, where the identity and
composition is induced from `C`. -/
@[ext]
structure Hom (X Y : InducedBicategory C F) where
  /-- Construct a morphism in `InducedBicategory C F` from a morhism in `C`. -/
  mkHom ::
  /-- The morphism in `C` underlying the morphism in `InducedBicategory C F`. -/
  hom : F X ⟶ F Y

@[simps id_hom comp_hom]
instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[ext]
lemma hom_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- `InducedBicategory.Hom X Y` is the type of morphisms between `X` and `Y` viewed as objects of
the bicategory `B`. This is given a `CategoryStruct` instance below, where the identity and
composition is induced from `C`. -/
@[ext]
structure Hom₂ {X Y : InducedBicategory C F} (f g : X ⟶ Y) where
  /-- The 2-morphism in `C` underlying the 2-morphism in `InducedBicategory C F`. -/
  hom : f.hom ⟶ g.hom

@[simps!]
instance Hom.category (X Y : InducedBicategory C F) : Category (X ⟶ Y) where
  Hom f g := Hom₂ f g
  id f := ⟨𝟙 f.hom⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

@[ext]
lemma hom₂_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} {η θ : f ⟶ g} (h : η.hom = θ.hom) :
    η = θ :=
  Hom₂.ext h

/-- Synonym for constructor of `Hom2` where the 1-morphisms `f` and `g` lie in `B` and not `Bᵒᵖ`. -/
@[simps]
def mkHom₂ {a b : InducedBicategory C F} {f g : a ⟶ b} (η : f.hom ⟶ g.hom) : f ⟶ g :=
  ⟨η⟩

/-- Constructor for 2-isomorphisms in the induced bicategory. -/
@[simps!]
def isoMk {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom) : f ≅ g where
  hom := mkHom₂ φ.hom
  inv := mkHom₂ φ.inv

@[simps!]
instance bicategory : Bicategory (InducedBicategory C F) where
  __ := categoryStruct
  whiskerLeft {_ _ _} h {_ _} η := mkHom₂ <| h.hom ◁ Hom₂.hom η
  whiskerRight {_ _ _} {_ _} η h := mkHom₂ <| (Hom₂.hom η) ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (λ_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange {_ _ _ _ _ _ _} η θ := by ext; simp; exact whisker_exchange _ _

attribute [-simp] bicategory_comp_hom bicategory_Hom

section

/-- The forgetful pseudofunctor from an induced bicategory to the original bicategory,
forgetting the extra data.
-/
@[simps!]
def inducedPseudofunctor : StrictPseudofunctor (InducedBicategory C F) C :=
  StrictPseudofunctor.mk' {
    obj X := F X
    map f := f.hom
    map₂ η := η.hom }

end

section

@[simp]
lemma eqToHom_hom {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f = g) :
    (eqToHom h).hom = eqToHom (h ▸ rfl) := by
  subst h; simp only [eqToHom_refl, Hom.category_id_hom]

@[simp]
lemma mkHom_eqToHom {X Y : InducedBicategory C F} {f g : F X ⟶ F Y} (h : f = g) :
    mkHom₂ (eqToHom h) = eqToHom (h ▸ rfl) := by
  ext; subst h; simp only [eqToHom_refl, mkHom₂_hom, Hom.category_id_hom]

variable [Strict C]

attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso

instance : Strict (InducedBicategory C F) where

end

end InducedBicategory

end CategoryTheory.Bicategory
