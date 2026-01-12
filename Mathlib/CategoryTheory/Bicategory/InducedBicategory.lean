/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!

# Induced bicategories

In this file we develop API for constructing a full sub-bicategory of a bicategory `C`, given a
map `F : B → C`. The objects of the induced bicategory are the objects of `B`, while the
1-morphisms and 2-morphisms are taken as all corresponding morphisms in `C`.

## TODO

One might also want to develop "locally induced" bicategories, which should allow for a sub-class
of 1-morphisms as well. However, this needs more thought. If one tries the naive approach of simply
replacing the map `F` below with a "functor" (between `CategoryStruct`s), one runs into the issue
that `map_comp` and `map_id` might not be definitional equalities (which they should be in
practice). Hence one needs to carefully carry these around, or specify `F` in a way that ensures
they are def-eqs, perhaps constructing it from specified `MorphismProperty`s.
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

set_option backward.privateInPublic true in
/-- `InducedBicategory.Hom X Y` is a type-alias for morphisms between `X Y : B` viewed as objects
of `B` with the induced bicategory structure. This is given a `CategoryStruct` instance below,
where the identity and composition is induced from `C`. -/
@[ext]
structure Hom (X Y : InducedBicategory C F) where
  private mk ::
  /-- The morphism in `C` underlying the morphism in `InducedBicategory C F`. -/
  hom : F X ⟶ F Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
@[simps id_hom comp_hom]
instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom X Y := Hom X Y
  id X := ⟨𝟙 (F X)⟩
  comp u v := ⟨u.hom ≫ v.hom⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Synonym for `Hom.mk` which makes unification easier. -/
abbrev mkHom {X Y : InducedBicategory C F} (f : F X ⟶ F Y) : X ⟶ Y :=
  ⟨f⟩

@[ext]
lemma hom_ext {X Y : InducedBicategory C F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

/-- `InducedBicategory.Hom₂ f g` is a type-alias for 2-morphisms between `f g : X ⟶ Y`, where
`f` and `g` are 1-morphisms for the induced bicategory structure on `B`.

This is given a `Category` instance below, induced from the corresponding one in `C`. -/
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

/-- Synonym for the constructor of `Hom₂` where the 1-morphisms `f` and `g` lie in `C`, and not
given in the form `f'.hom`, `g'.hom` for some `f' g' : InducedBicategory.Hom _ _`. -/
abbrev mkHom₂ {a b : InducedBicategory C F} {f g : F a ⟶ F b} (η : f ⟶ g) : mkHom f ⟶ mkHom g :=
  Hom₂.mk η

/-- Constructor for 2-isomorphisms in the induced bicategory. -/
@[simps!]
def isoMk {X Y : InducedBicategory C F} {f g : X ⟶ Y} (φ : f.hom ≅ g.hom) : f ≅ g where
  hom := ⟨φ.hom⟩
  inv := ⟨φ.inv⟩

@[simps!]
instance bicategory : Bicategory (InducedBicategory C F) where
  whiskerLeft {_ _ _} h {_ _} η := mkHom₂ <| h.hom ◁ Hom₂.hom η
  whiskerRight {_ _ _} {_ _} η h := mkHom₂ <| (Hom₂.hom η) ▷ h.hom
  associator x y z := isoMk (α_ x.hom y.hom z.hom)
  leftUnitor x := isoMk (λ_ x.hom)
  rightUnitor x := isoMk (ρ_ x.hom)
  whisker_exchange {_ _ _ _ _ _ _} η θ := by ext; simpa using whisker_exchange _ _

attribute [-simp] bicategory_comp_hom bicategory_Hom

section

/-- The forgetful (strict) pseudofunctor from an induced bicategory to the original bicategory,
forgetting the extra data.
-/
@[simps!]
def forget : StrictPseudofunctor (InducedBicategory C F) C :=
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
  ext; subst h; simp only [eqToHom_refl, Hom.category_id_hom]

variable [Strict C]

attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso

instance : Strict (InducedBicategory C F) where

end

end InducedBicategory

end CategoryTheory.Bicategory
