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
A subtype-like structure for full subbicategories. 1- and 2-morphisms ignore the property. We
don't use actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
sub(bi)categories. -/
@[ext]
structure FullSubbicategory (P : ObjectProperty B) where
  /-- The bicategory of which this is a full subbicategory -/
  obj : B
  /-- The predicate satisfied by all objects in this subbicategory -/
  property : P obj

namespace FullSubbicategory

section

variable (P : ObjectProperty B)

-- TODO: Should bicategory_Hom should be a simp projection?
@[simps!]
instance bicategory : Bicategory.{w, v} (FullSubbicategory P) :=
  InducedBicategory.bicategory FullSubbicategory.obj

/-- The forgetful strict pseudofunctor from a full subbicategory into the original bicategory
("forgetting" the condition). -/
@[simps!]
def forget : StrictPseudofunctor (FullSubbicategory P) B :=
  InducedBicategory.forget FullSubbicategory.obj

variable {P}

/-- Construct a morphism in `FullSubbicategory P` from a morhism in `B`. -/
abbrev mkHom {a b : FullSubbicategory P} (f : a.obj ⟶ b.obj) : a ⟶ b :=
  InducedBicategory.mkHom f

/-- Construct a 2-morphism in `FullSubbicategory P` from a 2-morhism in `B`, where the corresponding
objects lie in the full subbicategory. -/
abbrev mkHom₂ {a b : FullSubbicategory P} {f g : a.obj ⟶ b.obj} (η : f ⟶ g) :
    mkHom f ⟶ mkHom g :=
  InducedBicategory.mkHom₂ η

@[ext]
abbrev hom₂_ext {a b : FullSubbicategory P} {f g : a ⟶ b} {η θ : f ⟶ g} (h : η.hom = θ.hom) :
    η = θ :=
  InducedBicategory.hom₂_ext h

/-- Constructor for 2-isomorphisms in `FullSubbicategory P` when the underlying objects
lie in `FullSubbicategory P`. -/
@[simps]
def isoMk {X Y : FullSubbicategory P} {f g : X.obj ⟶ Y.obj} (e : f ≅ g) :
    mkHom f ≅ mkHom g where
  hom := mkHom₂ e.hom
  inv := mkHom₂ e.inv
  hom_inv_id := hom₂_ext <| e.hom_inv_id
  inv_hom_id := hom₂_ext <| e.inv_hom_id

variable {P' : ObjectProperty B}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced strict pseudofunctor `FullSubbicategory P ⥤ᵖ FullSubbicategory P'`. -/
@[simps!]
def ιOfLE (h : P ≤ P') : StrictPseudofunctor (FullSubbicategory P) (FullSubbicategory P') :=
  StrictPseudofunctor.mk' {
    obj X := ⟨X.1, h _ X.2⟩
    map f := mkHom f.hom
    map₂ η := mkHom₂ η.hom }

end

section lift

variable {C : Type u'} [Bicategory.{w', v'} C] (P Q : ObjectProperty C)
  (F : B ⥤ᵖ C) (hF : ∀ X, P (F.obj X))

/-- A pseudofunctor which maps objects to objects satisfying a certain property induces a lift
through the full subbicategory of objects satisfying that property. -/
@[simps]
def lift : B ⥤ᵖ FullSubbicategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := mkHom (F.map f)
  map₂ η := mkHom₂ (F.map₂ η)
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
