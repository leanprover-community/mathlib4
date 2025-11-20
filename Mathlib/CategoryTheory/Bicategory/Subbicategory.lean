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
a bicategory structure on the type `P.FullSubbicategory`
of objects in `B` satisfying `P`.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

-- TODO: wrong namespace?
namespace ObjectProperty

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

section

variable (P : ObjectProperty B)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories. -/
@[ext]
structure FullSubbicategory where
  /-- The category of which this is a full subcategory -/
  obj : B
  /-- The predicate satisfied by all objects in this subcategory -/
  property : P obj

instance FullSubbicategory.bicategory : Bicategory.{w, v} P.FullSubbicategory :=
  InducedBicategory.bicategory FullSubbicategory.obj

-- these lemmas are not particularly well-typed, so would probably be dangerous as simp lemmas

lemma FullSubbicategory.id_def (X : P.FullSubbicategory) : 𝟙 X = ⟨𝟙 X.obj⟩ := rfl

lemma FullSubbicategory.comp_def {X Y Z : P.FullSubbicategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def ι₂ : StrictPseudofunctor P.FullSubbicategory B :=
  InducedBicategory.forget FullSubbicategory.obj

@[simp]
theorem ι₂_obj {X} : P.ι₂.obj X = X.obj :=
  rfl

@[simp]
theorem ι₂_map {X Y} {f : X ⟶ Y} : P.ι₂.map f = f.hom := -- TODO: right statement?
  rfl

-- TODO: need to think more from here

/-- Constructor for isomorphisms in `P.FullSubbicategory` when
`P : ObjectProperty C`. -/
@[simps]
def isoMk' {X Y : P.FullSubbicategory} (e : P.ι₂.obj X ≅ P.ι₂.obj Y) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id


variable {P} {P' : ObjectProperty C}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `P.FullSubbicategory ⥤ P'.FullSubbicategory`. -/
@[simps]
def ιOfLE (h : P ≤ P') : P.FullSubbicategory ⥤ P'.FullSubbicategory where
  obj X := ⟨X.1, h _ X.2⟩
  map f := f

/-- If `h : P ≤ P'`, then `ιOfLE h` is fully faithful. -/
def fullyFaithfulιOfLE (h : P ≤ P') :
    (ιOfLE h).FullyFaithful where
  preimage f := f

instance full_ιOfLE (h : P ≤ P') : (ιOfLE h).Full := (fullyFaithfulιOfLE h).full
instance faithful_ιOfLE (h : P ≤ P') : (ιOfLE h).Faithful := (fullyFaithfulιOfLE h).faithful

/-- If `h : P ≤ P'` is an inequality of properties of objects,
this is the obvious isomorphism `ιOfLE h ⋙ P'.ι ≅ P.ι`. -/
def ιOfLECompιIso (h : P ≤ P') : ιOfLE h ⋙ P'.ι ≅ P.ι := Iso.refl _

end

section lift

variable {D : Type u'} [Category.{v'} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : ∀ X, P (F.obj X))

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def lift : C ⥤ FullSubbicategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := F.map f

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. This is actually true definitionally. -/
def liftCompιIso : P.lift F hF ⋙ P.ι ≅ F := Iso.refl _

@[simp]
lemma ι_obj_lift_obj (X : C) :
    P.ι.obj ((P.lift F hF).obj X) = F.obj X := rfl

@[simp]
lemma ι_obj_lift_map {X Y : C} (f : X ⟶ Y) :
    P.ι.map ((P.lift F hF).map f) = F.map f := rfl

instance [F.Faithful] : (P.lift F hF).Faithful :=
  Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)

instance [F.Full] : (P.lift F hF).Full :=
  Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

variable {Q}

/-- When `h : P ≤ Q`, this is the canonical isomorphism
`P.lift F hF ⋙ ιOfLE h ≅ Q.lift F _`. -/
def liftCompιOfLEIso (h : P ≤ Q) :
    P.lift F hF ⋙ ιOfLE h ≅ Q.lift F (fun X ↦ h _ (hF X)) := Iso.refl _

end lift

end ObjectProperty

end CategoryTheory
