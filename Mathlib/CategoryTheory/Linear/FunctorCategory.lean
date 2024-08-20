/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

import Batteries.Tactic.ShowUnused

/-!
# Linear structure on functor categories

If `C` and `D` are categories and `D` is `R`-linear,
then `C ⥤ D` is also `R`-linear.

-/

universe w v u v' u' v₁ v₂ v₃ u₁ u₂ u₃

noncomputable
section Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

open CategoryTheory

open CategoryTheory.Category

open scoped Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : ∀ X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by aesop_cat
  /-- `0` composed with `f` is `0` -/
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by aesop_cat

attribute [instance] HasZeroMorphisms.zero

variable {C}

@[simp]
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z

@[simp]
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f

open Opposite HasZeroMorphisms

end CategoryTheory.Limits

end Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

section Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q) := by infer_instance
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g := by
    aesop_cat
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g' := by
    aesop_cat

attribute [inherit_doc Preadditive] Preadditive.homGroup Preadditive.add_comp Preadditive.comp_add

attribute [instance] Preadditive.homGroup

-- Porting note: simp can prove reassoc version
attribute [simp] Preadditive.add_comp

-- (the linter doesn't like `simp` on this lemma)
attribute [simp] Preadditive.comp_add

end CategoryTheory

open CategoryTheory

namespace CategoryTheory

namespace Preadditive

section Preadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Preadditive C]

section InducedCategory

variable {D : Type u'} (F : D → C)

end InducedCategory

/-- Composition by a fixed left argument as a group homomorphism -/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
  mk' (fun g => f ≫ g) fun g g' => by simp

/-- Composition by a fixed right argument as a group homomorphism -/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
  mk' (fun f => f ≫ g) fun f f' => by simp

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

-- Porting note: simp can prove the reassoc version
@[simp]
theorem sub_comp : (f - f') ≫ g = f ≫ g - f' ≫ g :=
  map_sub (rightComp P g) f f'

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[simp]
theorem comp_sub : f ≫ (g - g') = f ≫ g - f ≫ g' :=
  map_sub (leftComp R f) g g'

-- Porting note: simp can prove the reassoc version
@[simp]
theorem neg_comp : (-f) ≫ g = -f ≫ g :=
  map_neg (rightComp P g) f

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[simp]
theorem comp_neg : f ≫ (-g) = -f ≫ g :=
  map_neg (leftComp R f) g

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

open ZeroObject

variable [HasZeroObject C]

end Preadditive

end Preadditive

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Preadditive.Basic

namespace CategoryTheory

open CategoryTheory.Limits Preadditive

variable {C D : Type*} [Category C] [Category D] [Preadditive D]

instance {F G : C ⥤ D} : Zero (F ⟶ G) where
  zero := { app := fun X => 0 }

instance {F G : C ⥤ D} : Add (F ⟶ G) where
  add α β :=
  { app := fun X => α.app X + β.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_add, NatTrans.naturality, add_comp] }

instance {F G : C ⥤ D} : Neg (F ⟶ G) where
  neg α :=
  { app := fun X => -α.app X,
    naturality := by 
      intro X Y f
      simp_all only [comp_neg, NatTrans.naturality, neg_comp] }

instance functorCategoryPreadditive : Preadditive (C ⥤ D) where
  homGroup F G :=
    { nsmul := nsmulRec
      zsmul := zsmulRec
      sub := fun α β => { app := fun X => α.app X - β.app X }
      add_assoc := by
        intros
        ext
        apply add_assoc
      zero_add := by
        intros
        dsimp
        ext
        apply zero_add
      add_zero := by
        intros
        dsimp
        ext
        apply add_zero
      add_comm := by
        intros
        dsimp
        ext
        apply add_comm
      sub_eq_add_neg := by
        intros
        dsimp
        ext
        apply sub_eq_add_neg
      neg_add_cancel := by
        intros
        dsimp
        ext
        apply neg_add_cancel }
  add_comp := by
    intros
    dsimp
    ext
    apply add_comp
  comp_add := by
    intros
    dsimp
    ext
    apply comp_add

end CategoryTheory

end Mathlib.CategoryTheory.Preadditive.Basic

section Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory.Limits

open LinearMap

namespace CategoryTheory

/-- A category is called `R`-linear if `P ⟶ Q` is an `R`-module such that composition is
    `R`-linear in both variables. -/
class Linear (R : Type w) [Semiring R] (C : Type u) [Category.{v} C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y) := by infer_instance
  /-- compatibility of the scalar multiplication with the post-composition -/
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g := by
    aesop_cat
  /-- compatibility of the scalar multiplication with the pre-composition -/
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g := by
    aesop_cat

attribute [instance] Linear.homModule

attribute [simp] Linear.smul_comp Linear.comp_smul

-- (the linter doesn't like `simp` on the `_assoc` lemma)
end CategoryTheory

end Mathlib.CategoryTheory.Linear.Basic

open CategoryTheory

namespace CategoryTheory

open CategoryTheory.Limits Linear
open CategoryTheory.Linear

variable {R : Type*} [Semiring R]
variable {C D : Type*} [Category C] [Category D] [Preadditive D] [Linear R D]

instance functorCategorySMul (F G : C ⥤ D) : SMul R (F ⟶ G) where
  smul r α := 
    { app := fun X => r • α.app X
      naturality := by
        intros
        rw [Linear.comp_smul, Linear.smul_comp, α.naturality] }

#adaptation_note
/--
At nightly-2024-08-08 we needed to significantly increase the maxHeartbeats here.
-/
set_option maxHeartbeats 60000 in
instance functorCategoryLinear : Linear R (C ⥤ D) where
  homModule F G :=
    { one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

instance functorCategoryLinear' : Linear R (C ⥤ D) where
  homModule F G :=
    { one_smul := by
        intros
        ext
        apply one_smul
      zero_smul := by
        intros
        ext
        apply zero_smul
      smul_zero := by
        intros
        ext
        apply smul_zero
      add_smul := by
        intros
        ext
        apply add_smul
      smul_add := by
        intros
        ext
        apply smul_add
      mul_smul := by
        intros
        ext
        apply mul_smul
        }
  smul_comp := by
    intros
    ext
    apply Linear.smul_comp
  comp_smul := by
    intros
    ext
    apply Linear.comp_smul

end CategoryTheory

#show_unused  CategoryTheory.functorCategoryLinear CategoryTheory.functorCategoryLinear'
