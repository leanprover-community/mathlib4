/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# Full subbicategories using object properties

Given a bicategory `B` and `P : ObjectProperty B`, we define
a bicategory structure on the type `FullSubbicategory P`
of objects in `B` satisfying `P`.

## TODO
This file could also define locally full subbicategories, where the user also specifies
the 1-morphisms using a morphism property.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

namespace Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories. -/
@[ext]
structure FullSubbicategory (P : ObjectProperty B) where
  /-- The category of which this is a full subcategory -/
  obj : B
  /-- The predicate satisfied by all objects in this subcategory -/
  property : P obj

namespace FullSubbicategory

section

variable (P : ObjectProperty B)

-- TODO: Should bicategory_Hom should be a simp projection?
@[simps!?]
instance bicategory : Bicategory.{w, v} (FullSubbicategory P) :=
  InducedBicategory.bicategory FullSubbicategory.obj

example {B : Type u} [inst : Bicategory B]
    (P : ObjectProperty B) {X Y Z : FullSubbicategory P} (u : X ⟶ Y)
        (v : Y ⟶ Z) : (u ≫ v).hom = u.hom ≫ v.hom := by
  simp only [bicategory_comp_hom]

/-
Q1: does the simps above having "wrong" type cause problems? Or is it fine?
Q3: Automation w/ aesop & whisker_exchange?

-/

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
@[simps!]
def forget : StrictPseudofunctor (FullSubbicategory P) B :=
  InducedBicategory.forget FullSubbicategory.obj

variable {P}

/-- Construct a morphism in `FullSubbicategory P` from a morhism in `B`. -/
abbrev mkHom₂ {a b : FullSubbicategory P} {f g : a ⟶ b} (η : f.hom ⟶ g.hom) : f ⟶ g :=
  InducedBicategory.mkHom₂ η

@[ext]
abbrev hom₂_ext {a b : FullSubbicategory P} {f g : a ⟶ b} {η θ : f ⟶ g}
    (h : η.hom = θ.hom) : η = θ :=
  InducedBicategory.hom₂_ext h

/-- Constructor for isomorphisms in `FullSubbicategory P` when
`P : ObjectProperty C`. -/
@[simps]
def isoMk {X Y : FullSubbicategory P} {f g : X ⟶ Y} (e : (forget P).map f ≅ (forget P).map g) :
    f ≅ g where
  hom := mkHom₂ e.hom
  inv := mkHom₂ e.inv
  hom_inv_id := hom₂_ext <| e.hom_inv_id
  inv_hom_id := hom₂_ext <| e.inv_hom_id


variable {P' : ObjectProperty B}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `FullSubbicategory P ⥤ FullSubbicategory P'`. -/
@[simps!]
def ιOfLE (h : P ≤ P') : StrictPseudofunctor (FullSubbicategory P) (FullSubbicategory P') :=
  StrictPseudofunctor.mk' {
    obj X := ⟨X.1, h _ X.2⟩
    map f := ⟨f.hom⟩
    map₂ η := mkHom₂ η.hom }

end

section lift

variable {C : Type u'} [Bicategory.{w', v'} C] (P Q : ObjectProperty C)
  (F : B ⥤ᵖ C) (hF : ∀ X, P (F.obj X))

/-- A pseudofunctor which maps objects to objects satisfying a certain property induces a lift
through the full subcategory of objects satisfying that property. -/
@[simps]
def lift : B ⥤ᵖ FullSubbicategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := ⟨F.map f⟩
  map₂ η :=mkHom₂ (F.map₂ η)
  mapId X := isoMk (F.mapId X)
  mapComp f g := isoMk (F.mapComp f g)

@[simp]
lemma ι_obj_lift_obj (X : B) :
    (forget P).obj ((lift P F hF).obj X) = F.obj X := rfl

@[simp]
lemma ι_obj_lift_map {X Y : B} (f : X ⟶ Y) :
    (forget P).map ((lift P F hF).map f) = F.map f := rfl

end lift

end FullSubbicategory

end Bicategory

end CategoryTheory
