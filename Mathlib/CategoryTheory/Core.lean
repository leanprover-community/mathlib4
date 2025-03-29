/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
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

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [CategoryTheory universes].
/-- The core of a category C is the groupoid whose morphisms are all the
isomorphisms of C. -/
def Core (C : Type u₁) := C

variable {C : Type u₁} [Category.{v₁} C]

instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : C) := X ≅ Y
  id (X : C) := Iso.refl X
  comp f g := Iso.trans f g
  inv {_ _} f := Iso.symm f

namespace Core

@[simp]
/- Porting note: abomination -/
theorem id_hom (X : C) : Iso.hom (coreCategory.id X) = @CategoryStruct.id C _ X := by
  rfl

@[simp]
theorem comp_hom {X Y Z : Core C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

@[ext]
theorem hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g := Iso.ext h

variable (C)

/-- The core of a category is naturally included in the category. -/
@[simps!]
def inclusion : Core C ⥤ C where
  obj := id
  map f := f.hom

-- Porting note: This worked without proof before.
instance : (inclusion C).Faithful where
  map_injective := by
    intro _ _
    apply Iso.ext

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
/-- A functor from a groupoid to a category C factors through the core of C. -/
def functorToCore (F : G ⥤ C) : G ⥤ Core C where
  obj X := F.obj X
  map f := { hom := F.map f, inv := F.map (Groupoid.inv f) }

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core C ⥤ C`.
-/
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
@[simps! hom_app inv_app]
def coreId : (𝟭 C).core ≅ 𝟭 (Core C) := Iso.refl _

/-- The core of the composition of F and G is the composition of the cores. -/
@[simps! hom_app inv_app]
def coreComp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
  (F ⋙ G).core ≅ F.core ⋙ G.core := Iso.refl _

end Functor

namespace Iso

variable {D : Type u₂} [Category.{v₂} D]

/-- A natural isomorphism of functors induces a natural isomorphism between their cores. -/
@[simps! hom_app inv_app]
def core {F G : C ⥤ D} (α : F ≅ G) : F.core ≅ G.core :=
  NatIso.ofComponents
    (fun x ↦ Groupoid.isoEquivHom _ _|>.symm <| α.app x)
    (fun {_ _} f ↦ by aesop_cat)

@[simp]
lemma coreComp {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) : (α ≪≫ β).core = α.core ≪≫ β.core := rfl

@[simp]
lemma coreId {F : C ⥤ D} : (Iso.refl F).core = Iso.refl F.core := rfl

-- Arguments order and simp normal forms here are chosen to mimic simp lemmas of pseudofunctors.

@[simp]
lemma coreWhiskerLeft {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H) :
    (isoWhiskerLeft F η).core =
    F.coreComp G ≪≫ isoWhiskerLeft F.core η.core ≪≫ (F.coreComp H).symm := by
  aesop_cat

@[simp]
lemma coreWhiskerRight {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E) :
    (isoWhiskerRight η H ).core =
    F.coreComp H ≪≫ isoWhiskerRight η.core H.core ≪≫ (G.coreComp H).symm := by
  aesop_cat

@[simp]
lemma coreLeftUnitor {F : C ⥤ D} :
    F.leftUnitor.core =
    (𝟭 C).coreComp F ≪≫ isoWhiskerRight (Functor.coreId C) _ ≪≫ F.core.leftUnitor := by
  aesop_cat

@[simp]
lemma coreRightUnitor {F : C ⥤ D} :
    F.rightUnitor.core =
    (F).coreComp (𝟭 D) ≪≫ isoWhiskerLeft _ (Functor.coreId D) ≪≫ F.core.rightUnitor := by
  aesop_cat

@[simp]
lemma coreAssociator {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (Functor.associator F G H).core =
    (F ⋙ G).coreComp H ≪≫ isoWhiskerRight (F.coreComp G) H.core ≪≫
      Functor.associator F.core G.core H.core ≪≫ (isoWhiskerLeft F.core (G.coreComp H)).symm ≪≫
      (F.coreComp (G ⋙ H)).symm
      := by
  aesop_cat

end Iso

namespace Functor

variable {D : Type u₂} [Category.{v₂} D]

/-- Taking the core of a functor is functorial if we discard non-invertible natural
transformations. -/
@[simps!]
def coreFunctor : Core (C ⥤ D) ⥤ Core C ⥤ Core D where
  obj F := F.core
  map η := η.core.hom

end Functor

end

/-- `ofEquivFunctor m` lifts a type-level `EquivFunctor`
to a categorical functor `Core (Type u₁) ⥤ Core (Type u₂)`.
-/
def ofEquivFunctor (m : Type u₁ → Type u₂) [EquivFunctor m] : Core (Type u₁) ⥤ Core (Type u₂) where
  obj := m
  map f := (EquivFunctor.mapEquiv m f.toEquiv).toIso
  map_id α := by apply Iso.ext; funext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    apply Iso.ext; funext x; dsimp
    erw [Iso.toEquiv_comp]
    rw [EquivFunctor.map_trans', Function.comp]

end CategoryTheory
