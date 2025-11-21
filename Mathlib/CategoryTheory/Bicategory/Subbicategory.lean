/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.InducedBicategory
public import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# The full subbicategory associated to a property of objects

Given a bicategory `B` and `P : ObjectProperty B`, we define
a bicategory structure on the type `FullSubbicategory P`
of objects in `B` satisfying `P`.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

-- TODO: wrong namespace?
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

instance bicategory : Bicategory.{w, v} (FullSubbicategory P) :=
  InducedBicategory.bicategory FullSubbicategory.obj

abbrev mkHom₂ {a b : FullSubbicategory P} {f g : a ⟶ b} (η : f.hom ⟶ g.hom) : f ⟶ g :=
  InducedBicategory.mkHom₂ η

-- these lemmas are not particularly well-typed, so would probably be dangerous as simp lemmas

lemma id_def (X : FullSubbicategory P) : 𝟙 X = ⟨𝟙 X.obj⟩ := rfl

lemma comp_def {X Y Z : FullSubbicategory P} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def forget : StrictPseudofunctor (FullSubbicategory P) B :=
  InducedBicategory.forget FullSubbicategory.obj

@[simp]
theorem forget_obj {X} : (forget P).obj X = X.obj :=
  rfl

@[simp]
theorem forget_map {X Y} {f : X ⟶ Y} : (forget P).map f = f.hom := -- TODO: right statement?
  rfl

/-- Constructor for isomorphisms in `FullSubbicategory P` when
`P : ObjectProperty C`. -/
@[simps]
def isoMk {X Y : FullSubbicategory P} {f g : X ⟶ Y} (e : (forget P).map f ≅ (forget P).map g) :
    f ≅ g where
  hom := InducedBicategory.mkHom₂ e.hom -- TODO: need mkHom₂ in this namespace
  inv := InducedBicategory.mkHom₂ e.inv
  hom_inv_id := InducedBicategory.hom₂_ext <| e.hom_inv_id
  inv_hom_id := InducedBicategory.hom₂_ext <| e.inv_hom_id


variable {P} {P' : ObjectProperty B}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `FullSubbicategory P ⥤ P'.FullSubbicategory`. -/
@[simps!]
def ιOfLE (h : P ≤ P') : StrictPseudofunctor (FullSubbicategory P) (FullSubbicategory P') :=
  StrictPseudofunctor.mk' {
    obj X := ⟨X.1, h _ X.2⟩
    map f := ⟨f.hom⟩
    map₂ η := InducedBicategory.mkHom₂ η.hom }

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
  map₂ η := InducedBicategory.mkHom₂ (F.map₂ η)
  mapId X := isoMk P (F.mapId X) -- TODO: P should be implicit
  mapComp f g := isoMk P (F.mapComp f g)

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
