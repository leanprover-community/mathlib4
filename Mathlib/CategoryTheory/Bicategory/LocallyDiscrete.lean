/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Bicategory.Functor
import Mathlib.CategoryTheory.Bicategory.Strict

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
def LocallyDiscrete (C : Type u) :=
  C
#align category_theory.locally_discrete CategoryTheory.LocallyDiscrete

namespace LocallyDiscrete

instance [Inhabited C] : Inhabited (LocallyDiscrete C) := ⟨(default : C)⟩

instance [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C)
    where
  Hom := fun X Y : C => Discrete (X ⟶ Y)
  id := fun X : C => ⟨𝟙 X⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

instance (priority := 900) homSmallCategory (X Y : LocallyDiscrete C) : SmallCategory (X ⟶ Y) :=
  let X' : C := X
  let Y' : C := Y
  CategoryTheory.discreteCategory (X' ⟶ Y')
#align category_theory.locally_discrete.hom_small_category CategoryTheory.LocallyDiscrete.homSmallCategory

-- Porting note: Manually adding this instance (inferInstance doesn't work)
instance subsingleton2Hom {X Y : LocallyDiscrete C} (f g : X ⟶ Y) : Subsingleton (f ⟶ g) :=
  let X' : C := X
  let Y' : C := Y
  let f' : Discrete (X' ⟶ Y') := f
  let g' : Discrete (X' ⟶ Y') := g
  show Subsingleton (f' ⟶ g') from inferInstance

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext _ _ η.1.1
#align category_theory.locally_discrete.eq_of_hom CategoryTheory.LocallyDiscrete.eq_of_hom

end LocallyDiscrete

variable (C) [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C)
    where
  whiskerLeft f g h η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η h := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator f g h :=
    eqToIso <| by
      apply Discrete.ext
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

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C)
    where
  id_comp := by
    intros
    apply Discrete.ext
    apply Category.id_comp
  comp_id := by
    intros
    apply Discrete.ext
    apply Category.comp_id
  assoc := by
    intros
    apply Discrete.ext
    apply Category.assoc
#align category_theory.locally_discrete_bicategory.strict CategoryTheory.locallyDiscreteBicategory.strict

variable {I : Type u₁} [Category.{v₁} I] {B : Type u₂} [Bicategory.{w₂, v₂} B] [Strict B]

/--
If `B` is a strict bicategory and `I` is a (1-)category, any functor (of 1-categories) `I ⥤ B` can
be promoted to an oplax functor from `LocallyDiscrete I` to `B`.
-/
@[simps]
def Functor.toOplaxFunctor (F : I ⥤ B) : OplaxFunctor (LocallyDiscrete I) B
    where
  obj := F.obj
  map f := F.map f.as
  map₂ η := eqToHom (congr_arg _ (LocallyDiscrete.eq_of_hom η))
  mapId i := eqToHom (F.map_id i)
  mapComp f g := eqToHom (F.map_comp f.as g.as)
#align category_theory.functor.to_oplax_functor CategoryTheory.Functor.toOplaxFunctor

end CategoryTheory
