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
theorem mk_as (a : LocallyDiscrete C) : LocallyDiscrete.mk a.as = a := rfl

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
  Hom := fun X Y => Discrete (X.as ⟶ Y.as)
  id := fun X => ⟨𝟙 X.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

instance (priority := 900) homSmallCategory (X Y : LocallyDiscrete C) : SmallCategory (X ⟶ Y) :=
  CategoryTheory.discreteCategory (X.as ⟶ Y.as)
#align category_theory.locally_discrete.hom_small_category CategoryTheory.LocallyDiscrete.homSmallCategory

-- Porting note: Manually adding this instance (inferInstance doesn't work)
instance subsingleton2Hom {X Y : LocallyDiscrete C} (f g : X ⟶ Y) : Subsingleton (f ⟶ g) :=
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
  associator f g h :=
    eqToIso <| by
      apply Discrete.ext
      -- TODO: API should deal with this
      change (f.as ≫ g.as) ≫ h.as = f.as ≫ (g.as ≫ h.as)
      rw [Category.assoc]
  leftUnitor f :=
    eqToIso <| by
      apply Discrete.ext
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp]
  rightUnitor f :=
    eqToIso <| by
      apply Discrete.ext
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id]
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

open CategoryTheory Bicategory Discrete

universe w₂ v v₁ v₂ u u₁ u₂

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]
variable {F : Pseudofunctor (LocallyDiscrete I) B}

def Quiver.Hom.toLoc {a b : I} (f : a ⟶ b) : LocallyDiscrete.mk a ⟶ LocallyDiscrete.mk b := ⟨f⟩

-- @[simp]
-- lemma toLoc.id (a : I) : (𝟙 a).toLoc = 𝟙 (toLoc a) := by
--   rfl

-- TODO: these should be stated with {a b : LocallyDiscrete I}
-- have left them like this cuz they test the API going from I -> LocallyDiscrete I

-- Pseudofunctors from locally discrete categories to strict bicategories
lemma map₂_left_unitor' {a b : I} (f : a ⟶ b) : (F.mapComp (Discrete.mk (𝟙 a)) (Discrete.mk f)).inv =
    (F.mapId ⟨a⟩).hom ▷ F.map ⟨f⟩ ≫ eqToHom (by sorry) := by
  have h := F.map₂_left_unitor f.toLoc
  simp at h
  rw [F.map₂_eqToHom, ←Iso.inv_comp_eq, comp_eqToHom_iff] at h
  simp at h
  apply h

-- lemma map₂_right_unitor' {a b : I} (f : a ⟶ b) : (F.mapComp f.toLoc (𝟙 b).toLoc).inv =
--     F.map f.toLoc ◁ (F.mapId b).hom ≫ eqToHom (by simp) := by
--   have h := F.map₂_right_unitor f.toLoc
--   simp at h
--   rw [F.map₂_eqToHom, ←Iso.inv_comp_eq, comp_eqToHom_iff] at h
--   simp at h
--   apply h

-- lemma map₂_associator' {a b c d : I} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
--     (F.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).hom ≫ (F.map f.toLoc) ◁ (F.mapComp g.toLoc h.toLoc).hom
--     = eqToHom (by simp) ≫ (F.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).hom ≫
--     (F.mapComp f.toLoc g.toLoc).hom ▷ F.map h.toLoc ≫ eqToHom (by simp)
--     := by
--   have h := F.map₂_associator f.toLoc g.toLoc h.toLoc
--   simp at h
--   sorry
--   -- rw [F.map₂_eqToHom, Iso.eq_comp_inv, comp_eqToHom_iff] at h
