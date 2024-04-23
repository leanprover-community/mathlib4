/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Bicategory.Functor
import Mathlib.CategoryTheory.Bicategory.Strict
import Mathlib.CategoryTheory.Bicategory.EqToHom

#align_import category_theory.bicategory.locally_discrete from "leanprover-community/mathlib"@"c9c9fa15fec7ca18e9ec97306fb8764bfe988a7e"

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


universe w₂ v v₁ v₂ u u₁ u₂

variable {C : Type u}

/-- A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
@[ext]
structure LocallyDiscrete (C : Type u) where
  as : C

namespace LocallyDiscrete

@[simp]
theorem mk_as (a : LocallyDiscrete C) : mk a.as = a := rfl

@[simps]
def locallyDiscreteEquiv : LocallyDiscrete C ≃ C where
  toFun := LocallyDiscrete.as
  invFun := LocallyDiscrete.mk
  left_inv := by aesop_cat
  right_inv := by aesop_cat

instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq

instance [Inhabited C] : Inhabited (LocallyDiscrete C) := ⟨⟨default⟩⟩

-- TODO: figure out how to name these lemmas manually
@[simps]
instance [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C)
    where
  Hom := fun a b => Discrete (a.as ⟶ b.as)
  id := fun a => ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

-- TODO rename? Maybe dot notation with "toLoc" (I think dot notation is better)
@[simps]
def mkHom {a b : C} (f : a ⟶ b) : mk a ⟶ mk b := ⟨f⟩

@[simp]
lemma id_mk (a : C) : mkHom (𝟙 a) = 𝟙 (mk a) := rfl

@[simp]
lemma comp_mk {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    mkHom (f ≫ g) = mkHom f ≫ mkHom g := rfl

instance (priority := 900) homSmallCategory (a b : LocallyDiscrete C) : SmallCategory (a ⟶ b) :=
  CategoryTheory.discreteCategory (a.as ⟶ b.as)
#align category_theory.locally_discrete.hom_small_category CategoryTheory.LocallyDiscrete.homSmallCategory

-- Porting note: Manually adding this instance (inferInstance doesn't work)
instance subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext _ _ η.1.1
#align category_theory.locally_discrete.eq_of_hom CategoryTheory.LocallyDiscrete.eq_of_hom

end LocallyDiscrete

variable {C : Type u} [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory (C : Type u) [Category.{v} C] : Bicategory (LocallyDiscrete C)
    where
  whiskerLeft f g h η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η h := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator f g h := eqToIso <| by apply Discrete.ext; simp
  leftUnitor f := eqToIso <| by apply Discrete.ext; simp
  rightUnitor f := eqToIso <| by apply Discrete.ext; simp
#align category_theory.locally_discrete_bicategory CategoryTheory.locallyDiscreteBicategory

@[simp]
lemma LocallyDiscrete.id_comp {a b : LocallyDiscrete C} (f : a ⟶ b) : 𝟙 a ≫ f = f := by
  apply Discrete.ext
  apply Category.id_comp

@[simp]
lemma LocallyDiscrete.comp_id {a b : LocallyDiscrete C} (f : a ⟶ b) : f ≫ 𝟙 b = f := by
  apply Discrete.ext
  apply Category.comp_id

@[simp]
lemma LocallyDiscrete.assoc {a b c d : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Discrete.ext _ _ (Category.assoc _ _ _)

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C)
    where
  id_comp f := LocallyDiscrete.id_comp f
  comp_id f := LocallyDiscrete.comp_id f
  assoc f g h := LocallyDiscrete.assoc f g h
#align category_theory.locally_discrete_bicategory.strict CategoryTheory.locallyDiscreteBicategory.strict


variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `LocallyDiscrete I` to `B`.
-/
@[simps]
def Functor.toOplaxFunctor (F : I ⥤ B) : OplaxFunctor (LocallyDiscrete I) B
    where
  obj i := F.obj i.as
  map f := F.map f.as
  map₂ η := eqToHom (congr_arg _ (LocallyDiscrete.eq_of_hom η))
  mapId i := eqToHom (F.map_id i.as)
  mapComp f g := eqToHom (F.map_comp f.as g.as)
#align category_theory.functor.to_oplax_functor CategoryTheory.Functor.toOplaxFunctor

end CategoryTheory

open CategoryTheory Bicategory Discrete LocallyDiscrete

universe w₂ v v₁ v₂ u u₁ u₂

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]
variable {F : Pseudofunctor (LocallyDiscrete I) B}

-- These should be stated in terms of strict bicategories

-- Pseudofunctors from locally discrete categories to strict bicategories
lemma map₂_left_unitor' {a b : I} (f : a ⟶ b) : (F.mapComp (mkHom (𝟙 a)) (mkHom f)).inv =
    (F.mapId ⟨a⟩).hom ▷ F.map (mkHom f) ≫ eqToHom (by simp) := by
  have h := F.map₂_left_unitor (mkHom f)
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq, comp_eqToHom_iff] at h
  simp at h
  apply h

lemma map₂_right_unitor' {a b : I} (f : a ⟶ b) : (F.mapComp (mkHom f) (mkHom (𝟙 b))).inv =
    F.map (mkHom f) ◁ (F.mapId ⟨b⟩).hom ≫ eqToHom (by simp) := by
  have h := F.map₂_right_unitor (mkHom f)
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq, comp_eqToHom_iff] at h
  simp at h
  apply h

lemma map₂_associator' {a b c d : I} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (mkHom f) ((mkHom g) ≫ (mkHom h))).hom ≫ (F.map (mkHom f)) ◁ (F.mapComp (mkHom g) (mkHom h)).hom
    = eqToHom (by simp) ≫ (F.mapComp ((mkHom f) ≫ (mkHom g)) (mkHom h)).hom ≫
    (F.mapComp (mkHom f) (mkHom g)).hom ▷ F.map (mkHom h) ≫ eqToHom (by simp)
    := by
  have h := F.map₂_associator (mkHom f) (mkHom g) (mkHom h)
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq] at h
  -- TODO: rewrite thing as inv then move to LHS (+ restate lemma to use this notation instead!)
  sorry
