/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno

! This file was ported from Lean 3 source module category_theory.bicategory.locally_discrete
! leanprover-community/mathlib commit c9c9fa15fec7ca18e9ec97306fb8764bfe988a7e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.DiscreteCategory
import Mathbin.CategoryTheory.Bicategory.Functor
import Mathbin.CategoryTheory.Bicategory.Strict

/-!
# Locally discrete bicategories

A category `C` can be promoted to a strict bicategory `locally_discrete C`. The objects and the
1-morphisms in `locally_discrete C` are the same as the objects and the morphisms, respectively,
in `C`, and the 2-morphisms in `locally_discrete C` are the equalities between 1-morphisms. In
other words, the category consisting of the 1-morphisms between each pair of objects `X` and `Y`
in `locally_discrete C` is defined as the discrete category associated with the type `X ⟶ Y`.
-/


namespace CategoryTheory

open Bicategory Discrete

open Bicategory

universe w₂ v v₁ v₂ u u₁ u₂

variable {C : Type u}

/-- A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def LocallyDiscrete (C : Type u) :=
  C
#align category_theory.locally_discrete CategoryTheory.LocallyDiscrete

namespace LocallyDiscrete

instance : ∀ [Inhabited C], Inhabited (LocallyDiscrete C) :=
  id

instance [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C)
    where
  Hom := fun X Y : C => Discrete (X ⟶ Y)
  id := fun X : C => ⟨𝟙 X⟩
  comp X Y Z f g := ⟨f.as ≫ g.as⟩

variable {C} [CategoryStruct.{v} C]

instance (priority := 900) homSmallCategory (X Y : LocallyDiscrete C) : SmallCategory (X ⟶ Y) :=
  CategoryTheory.discreteCategory (X ⟶ Y)
#align category_theory.locally_discrete.hom_small_category CategoryTheory.LocallyDiscrete.homSmallCategory

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  by
  have : discrete.mk f.as = discrete.mk g.as := congr_arg discrete.mk (eq_of_hom η)
  simpa using this
#align category_theory.locally_discrete.eq_of_hom CategoryTheory.LocallyDiscrete.eq_of_hom

end LocallyDiscrete

variable (C) [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C)
    where
  whiskerLeft X Y Z f g h η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight X Y Z f g η h := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator W X Y Z f g h :=
    eqToIso <| by
      unfold_projs
      simp only [category.assoc]
  leftUnitor X Y f :=
    eqToIso <| by
      unfold_projs
      simp only [category.id_comp, mk_as]
  rightUnitor X Y f :=
    eqToIso <| by
      unfold_projs
      simp only [category.comp_id, mk_as]
#align category_theory.locally_discrete_bicategory CategoryTheory.locallyDiscreteBicategory

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C)
    where
  id_comp' := by
    intros
    ext1
    unfold_projs
    apply category.id_comp
  comp_id' := by
    intros
    ext1
    unfold_projs
    apply category.comp_id
  assoc' := by
    intros
    ext1
    unfold_projs
    apply category.assoc
#align category_theory.locally_discrete_bicategory.strict CategoryTheory.locallyDiscreteBicategory.strict

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `locally_discrete I` to `B`.
-/
@[simps]
def Functor.toOplaxFunctor (F : I ⥤ B) : OplaxFunctor (LocallyDiscrete I) B
    where
  obj := F.obj
  map X Y f := F.map f.as
  zipWith i j f g η := eqToHom (congr_arg _ (eq_of_hom η))
  map_id i := eqToHom (F.map_id i)
  map_comp i j k f g := eqToHom (F.map_comp f.as g.as)
#align category_theory.functor.to_oplax_functor CategoryTheory.Functor.toOplaxFunctor

end CategoryTheory

