/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Strict

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `LocallyDiscrete C`. The objects and the
1-morphisms in `LocallyDiscrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `LocallyDiscrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `LocallyDiscrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/

namespace CategoryTheory

open Bicategory Discrete

open Bicategory

universe w₂ w₁ v₂ v₁ v u₂ u₁ u

section

variable {C : Type u}

/-- A wrapper for promoting any category to a bicategory,
with the only 2-morphisms being equalities.
-/
@[ext]
structure LocallyDiscrete (C : Type u) where
  /-- A wrapper for promoting any category to a bicategory,
  with the only 2-morphisms being equalities.
  -/
  as : C

namespace LocallyDiscrete

@[simp]
theorem mk_as (a : LocallyDiscrete C) : mk a.as = a := rfl

/-- `LocallyDiscrete C` is equivalent to the original type `C`. -/
@[simps]
def locallyDiscreteEquiv : LocallyDiscrete C ≃ C where
  toFun := LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq

instance [Inhabited C] : Inhabited (LocallyDiscrete C) :=
  ⟨⟨default⟩⟩

instance categoryStruct [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C) where
  Hom a b := Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

@[simp]
lemma id_as (a : LocallyDiscrete C) : (𝟙 a : Discrete (a.as ⟶ a.as)).as = 𝟙 a.as :=
  rfl

@[simp]
lemma comp_as {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).as = f.as ≫ g.as :=
  rfl

instance (priority := 900) homSmallCategory (a b : LocallyDiscrete C) : SmallCategory (a ⟶ b) :=
  CategoryTheory.discreteCategory (a.as ⟶ b.as)

-- Porting note: Manually adding this instance (inferInstance doesn't work)
instance subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext _ _ η.1.1

end LocallyDiscrete

variable (C)
variable [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft f g h η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η h := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator f g h := eqToIso <| by apply Discrete.ext; simp
  leftUnitor f := eqToIso <| by apply Discrete.ext; simp
  rightUnitor f := eqToIso <| by apply Discrete.ext; simp

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) where
  id_comp f := Discrete.ext _ _ (Category.id_comp _)
  comp_id f := Discrete.ext _ _ (Category.comp_id _)
  assoc f g h := Discrete.ext _ _ (Category.assoc _ _ _)

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to a pseudofunctor from `LocallyDiscrete I` to `B`.
-/
@[simps]
def Functor.toPseudoFunctor (F : I ⥤ B) : Pseudofunctor (LocallyDiscrete I) B where
  obj i := F.obj i.as
  map f := F.map f.as
  map₂ η := eqToHom (congr_arg _ (LocallyDiscrete.eq_of_hom η))
  mapId i := eqToIso (F.map_id i.as)
  mapComp f g := eqToIso (F.map_comp f.as g.as)

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `LocallyDiscrete I` to `B`.
-/
@[simps]
def Functor.toOplaxFunctor (F : I ⥤ B) : OplaxFunctor (LocallyDiscrete I) B where
  obj i := F.obj i.as
  map f := F.map f.as
  map₂ η := eqToHom (congr_arg _ (LocallyDiscrete.eq_of_hom η))
  mapId i := eqToHom (F.map_id i.as)
  mapComp f g := eqToHom (F.map_comp f.as g.as)

end

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

@[simp]
lemma PrelaxFunctor.map₂_eqToHom (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b} (h : f = g) :
    F.map₂ (eqToHom h) = eqToHom (F.congr_map h) := by
  subst h; simp only [eqToHom_refl, PrelaxFunctor.map₂_id]

end

end CategoryTheory

section

open CategoryTheory LocallyDiscrete

universe v u

namespace Quiver.Hom

variable {C : Type u} [CategoryStruct.{v} C]

/-- The 1-morphism in `LocallyDiscrete C` associated to a given morphism `f : a ⟶ b` in `C` -/
@[simps]
def toLoc {a b : C} (f : a ⟶ b) : LocallyDiscrete.mk a ⟶ LocallyDiscrete.mk b :=
  ⟨f⟩

@[simp]
lemma id_toLoc (a : C) : (𝟙 a).toLoc = 𝟙 (LocallyDiscrete.mk a) :=
  rfl

@[simp]
lemma comp_toLoc {a b c : C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).toLoc = f.toLoc ≫ g.toLoc :=
  rfl

end Quiver.Hom

@[simp]
lemma CategoryTheory.LocallyDiscrete.eqToHom_toLoc {C : Type u} [Category.{v} C] {a b : C}
    (h : a = b) : (eqToHom h).toLoc = eqToHom (congrArg LocallyDiscrete.mk h) := by
  subst h; rfl

end
