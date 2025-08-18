/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
import Mathlib.Control.EquivFunctor
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Types

/-!
# The core of a category

The core of a category `C` is the (non-full) subcategory of `C` consisting of all objects,
and all isomorphisms. We construct it as a `CategoryTheory.Groupoid`.

`CategoryTheory.Core.inclusion : Core C ⥤ C` gives the faithful inclusion into the original
category.

Any functor `F` from a groupoid `G` into `C` factors through `CategoryTheory.Core C`,
but this is not functorial with respect to `F`.
-/

namespace CategoryTheory

open Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [CategoryTheory universes].
/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
structure Core (C : Type u₁) where
  /-- The object of the base category underlying an object in `Core C`. -/
  of : C

variable {C : Type u₁} [Category.{v₁} C]

/-- The hom-type between two objects of `Core C`.
It is defined as a one-field structure to prevent defeq abuses. -/
@[ext]
structure CoreHom (X Y : Core C) where
  /-- The isomorphism of objects of `C` underlying a morphism in `Core C`. -/
  iso : X.of ≅ Y.of

@[simps!]
instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : Core C) := CoreHom X Y
  id (X : Core C) := .mk <| Iso.refl X.of
  comp f g := .mk <| Iso.trans f.iso g.iso
  inv {_ _} f := .mk <| Iso.symm f.iso

@[simp]
lemma coreCategory_comp_iso {x y z : Core C} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).iso = f.iso ≪≫ g.iso := rfl

namespace Core

variable (C) in
/-- The core of a category is naturally included in the category. -/
@[simps!]
def inclusion : Core C ⥤ C where
  obj := of
  map f := f.iso.hom

@[ext]
theorem hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f.iso.hom = g.iso.hom) :
    f = g := by
  apply CoreHom.ext
  exact Iso.ext h

variable (C)

instance : (inclusion C).Faithful where

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
/-- A functor from a groupoid to a category C factors through the core of C. -/
@[simps!]
def functorToCore (F : G ⥤ C) : G ⥤ Core C where
  obj X := .mk <| F.obj X
  map f := .mk <| { hom := F.map f, inv := F.map (Groupoid.inv f) }

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core C ⥤ C`.
-/
@[simps!]
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)

end Core

section

namespace Functor

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor `Core C ⥤ Core D`. -/
@[simps!]
def core (F : C ⥤ D) : Core C ⥤ Core D := Core.functorToCore (Core.inclusion _ ⋙ F)

variable (C) in
/-- The core of the identity functor is the identity functor on the cores. -/
@[simps!]
def coreId : (𝟭 C).core ≅ 𝟭 (Core C) := Iso.refl _

/-- The core of the composition of F and G is the composition of the cores. -/
@[simps!]
def coreComp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).core ≅ F.core ⋙ G.core := Iso.refl _

end Functor

namespace Iso

variable {D : Type u₂} [Category.{v₂} D]

/-- A natural isomorphism of functors induces a natural isomorphism between their cores. -/
@[simps!]
def core {F G : C ⥤ D} (α : F ≅ G) : F.core ≅ G.core :=
  NatIso.ofComponents
    (fun x ↦ Groupoid.isoEquivHom _ _|>.symm <| .mk <| α.app x.of)

@[simp]
lemma coreComp {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) : (α ≪≫ β).core = α.core ≪≫ β.core := rfl

@[simp]
lemma coreId {F : C ⥤ D} : (Iso.refl F).core = Iso.refl F.core := rfl

lemma coreWhiskerLeft {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H) :
    (isoWhiskerLeft F η).core =
    F.coreComp G ≪≫ isoWhiskerLeft F.core η.core ≪≫ (F.coreComp H).symm := by
  cat_disch

lemma coreWhiskerRight {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E) :
    (isoWhiskerRight η H ).core =
    F.coreComp H ≪≫ isoWhiskerRight η.core H.core ≪≫ (G.coreComp H).symm := by
  cat_disch

lemma coreLeftUnitor {F : C ⥤ D} :
    F.leftUnitor.core =
    (𝟭 C).coreComp F ≪≫ isoWhiskerRight (Functor.coreId C) _ ≪≫ F.core.leftUnitor := by
  cat_disch

lemma coreRightUnitor {F : C ⥤ D} :
    F.rightUnitor.core =
    (F).coreComp (𝟭 D) ≪≫ isoWhiskerLeft _ (Functor.coreId D) ≪≫ F.core.rightUnitor := by
  cat_disch

lemma coreAssociator {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (Functor.associator F G H).core =
    (F ⋙ G).coreComp H ≪≫ isoWhiskerRight (F.coreComp G) H.core ≪≫
      Functor.associator F.core G.core H.core ≪≫ (isoWhiskerLeft F.core (G.coreComp H)).symm ≪≫
      (F.coreComp (G ⋙ H)).symm := by
  cat_disch

end Iso

variable (D : Type u₂) [Category.{v₂} D]

namespace Equivalence

variable {D} in
/-- Equivalent categories have equivalent cores. -/
@[simps!]
def core (E : C ≌ D) : Core C ≌ Core D where
  functor := E.functor.core
  inverse := E.inverse.core
  unitIso := E.unitIso.core
  counitIso := E.counitIso.core

end Equivalence

variable (C) in
/-- Taking the core of a functor is functorial if we discard non-invertible natural
transformations. -/
@[simps!]
def coreFunctor : Core (C ⥤ D) ⥤ Core C ⥤ Core D where
  obj F := F.of.core
  map η := η.iso.core.hom

end

/-- `ofEquivFunctor m` lifts a type-level `EquivFunctor`
to a categorical functor `Core (Type u₁) ⥤ Core (Type u₂)`.
-/
def ofEquivFunctor (m : Type u₁ → Type u₂) [EquivFunctor m] : Core (Type u₁) ⥤ Core (Type u₂) where
  obj x := .mk <| m x.of
  map f := .mk <| (EquivFunctor.mapEquiv m f.iso.toEquiv).toIso
  map_id α := by ext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    ext
    simp [EquivFunctor.map_trans', Function.comp]

end CategoryTheory
