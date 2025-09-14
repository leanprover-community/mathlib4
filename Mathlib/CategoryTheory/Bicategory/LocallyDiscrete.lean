/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
import Mathlib.CategoryTheory.Discrete.Basic
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
  left_inv := by cat_disch
  right_inv := by cat_disch

instance [DecidableEq C] : DecidableEq (LocallyDiscrete C) :=
  locallyDiscreteEquiv.decidableEq

instance [Inhabited C] : Inhabited (LocallyDiscrete C) :=
  ⟨⟨default⟩⟩

-- abbrev Hom [CategoryStruct.{v} C] (a b : LocallyDiscrete C) : Type v :=
--   Discrete (a.as ⟶ b.as)

instance categoryStruct [CategoryStruct.{v} C] : CategoryStruct (LocallyDiscrete C) where
  Hom a b := Discrete (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.as ≫ g.as⟩

variable [CategoryStruct.{v} C]

abbrev mkHom {a b : C} (f : a ⟶ b) :
    mk a ⟶ mk b :=
  ⟨f⟩

@[simp]
lemma id_as (a : LocallyDiscrete C) : (𝟙 a : a ⟶ a).as = 𝟙 a.as :=
  rfl

@[simp]
lemma comp_as {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).as = f.as ≫ g.as :=
  rfl

instance (priority := 900) homSmallCategory (a b : LocallyDiscrete C) : SmallCategory (a ⟶ b) :=
  CategoryTheory.discreteCategory (a.as ⟶ b.as)

/-- This instance is used to see through the synonym `a ⟶ b = Discrete (a.as ⟶ b.as)`. -/
instance subsingleton2Hom {a b : LocallyDiscrete C} (f g : a ⟶ b) : Subsingleton (f ⟶ g) :=
  instSubsingletonDiscreteHom f g

/-- Extract the equation from a 2-morphism in a locally discrete 2-category. -/
theorem eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) : f = g :=
  Discrete.ext η.1.1

theorem eqToHom_eq_of_hom {X Y : LocallyDiscrete C} {f g : X ⟶ Y} (η : f ⟶ g) :
    η = eqToHom (eq_of_hom η) :=
  Subsingleton.elim _ _

end LocallyDiscrete

namespace LocallyDiscrete

variable [Category.{v} C]

def idIso (a : C) :
    mkHom (𝟙 a) ≅ 𝟙 (mk a) :=
  eqToIso rfl

def compIso {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    mkHom (f ≫ g) ≅ mkHom f ≫ mkHom g :=
  eqToIso rfl

end LocallyDiscrete

variable (C)
variable [Category.{v} C]

/-- The locally discrete bicategory on a category is a bicategory in which the objects and the
1-morphisms are the same as those in the underlying category, and the 2-morphisms are the
equalities between 1-morphisms.
-/
instance locallyDiscreteBicategory : Bicategory (LocallyDiscrete C) where
  whiskerLeft _ _ _ η := eqToHom (congr_arg₂ (· ≫ ·) rfl (LocallyDiscrete.eq_of_hom η))
  whiskerRight η _ := eqToHom (congr_arg₂ (· ≫ ·) (LocallyDiscrete.eq_of_hom η) rfl)
  associator f g h := eqToIso <| by apply Discrete.ext; simp
  leftUnitor f := eqToIso <| by apply Discrete.ext; simp
  rightUnitor f := eqToIso <| by apply Discrete.ext; simp

/-- A locally discrete bicategory is strict. -/
instance locallyDiscreteBicategory.strict : Strict (LocallyDiscrete C) where
  id_comp _ := Discrete.ext (Category.id_comp _)
  comp_id _ := Discrete.ext (Category.comp_id _)
  assoc _ _ _ := Discrete.ext (Category.assoc _ _ _)

end

namespace Bicategory

namespace LocallyDiscrete

theorem associator_hom {C : Type u} [Category.{v} C] {a b c d : LocallyDiscrete C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom = eqToHom (Category.assoc _ _ _) :=
  rfl

theorem associator_inv {C : Type u} [Category.{v} C] {a b c d : LocallyDiscrete C}
    (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv = eqToHom (Category.assoc _ _ _).symm :=
  rfl

theorem leftUnitor_hom {C : Type u} [Category.{v} C] {a b : LocallyDiscrete C} (f : a ⟶ b) :
    (λ_ f).hom = eqToHom (Category.id_comp _) :=
  rfl

theorem leftUnitor_inv {C : Type u} [Category.{v} C] {a b : LocallyDiscrete C} (f : a ⟶ b) :
    (λ_ f).inv = eqToHom (Category.id_comp _).symm :=
  rfl

theorem rightUnitor_hom {C : Type u} [Category.{v} C] {a b : LocallyDiscrete C} (f : a ⟶ b) :
    (ρ_ f).hom = eqToHom (Category.comp_id _) :=
  rfl

theorem rightUnitor_inv {C : Type u} [Category.{v} C] {a b : LocallyDiscrete C} (f : a ⟶ b) :
    (ρ_ f).inv = eqToHom (Category.comp_id _).symm :=
  rfl

end LocallyDiscrete

/-- A bicategory is locally discrete if the categories of 1-morphisms are discrete. -/
abbrev IsLocallyDiscrete (B : Type*) [Bicategory B] := ∀ (b c : B), IsDiscrete (b ⟶ c)

instance (C : Type*) [Category C] : IsLocallyDiscrete (LocallyDiscrete C) :=
  fun _ _ ↦ Discrete.isDiscrete _

instance (B : Type*) [Bicategory B] [IsLocallyDiscrete B] : Strict B where
  id_comp f := obj_ext_of_isDiscrete (leftUnitor f).hom
  comp_id f := obj_ext_of_isDiscrete (rightUnitor f).hom
  assoc f g h := obj_ext_of_isDiscrete (associator f g h).hom

end Bicategory

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
