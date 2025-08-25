/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Jakob von Raumer, Junyan Xu
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Module.Defs
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Pre-semiadditive categories

A pre-semiadditive category is a category in which `X ⟶ Y` is a commutative monoid in such a way
that composition of morphisms is linear in both variables.

This file contains a definition of pre-semiadditive category that directly encodes the definition
given above. The definition could also be phrased as follows: A pre-semiadditive category is a
category enriched over the monoidal category of commutative monoids.

## Main results

* Definition of pre-semiadditive categories and basic properties

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* https://ncatlab.org/nlab/show/biproduct#SemiadditiveCategories

## Tags

semiadditive, pre-semiadditive, Hom group
-/


universe v u

open CategoryTheory.Limits

namespace CategoryTheory

/-- A category is called pre-semiadditive if `P ⟶ Q` is a commutative monoid such that composition
is linear in both variables. -/
@[stacks 00ZY]
class Presemiadditive (C : Type u) [Category.{v} C] where
  homMonoid (P Q : C) : AddCommMonoid (P ⟶ Q) := by infer_instance
  protected zero_comp (P Q R : C) (g : Q ⟶ R) : (0 : P ⟶ Q) ≫ g = 0 := by cat_disch
  add_comp (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R) : (f + f') ≫ g = f ≫ g + f' ≫ g := by cat_disch
  protected comp_zero (P Q R : C) (f : P ⟶ Q) : f ≫ (0 : Q ⟶ R) = 0 := by cat_disch
  comp_add (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R) : f ≫ (g + g') = f ≫ g + f ≫ g' := by cat_disch

attribute [inherit_doc Presemiadditive] Presemiadditive.homMonoid

attribute [instance] Presemiadditive.homMonoid

-- simp can already prove reassoc version
attribute [reassoc, simp] Presemiadditive.add_comp

attribute [reassoc] Presemiadditive.comp_add

attribute [simp] Presemiadditive.comp_add

namespace Presemiadditive

open AddMonoidHom

variable {C : Type u} [Category.{v} C] [Presemiadditive C]

section InducedCategory

universe u'

variable {D : Type u'} (F : D → C)

instance inducedCategory : Presemiadditive.{v} (InducedCategory C F) where
  homMonoid P Q := @Presemiadditive.homMonoid C _ _ (F P) (F Q)
  zero_comp _ _ _ _ := Presemiadditive.zero_comp ..
  add_comp _ _ _ _ _ _ := add_comp ..
  comp_zero _ _ _ _ := Presemiadditive.comp_zero ..
  comp_add _ _ _ _ _ _ := comp_add ..

end InducedCategory

instance fullSubcategory (Z : ObjectProperty C) : Presemiadditive Z.FullSubcategory where
  homMonoid P Q := @Presemiadditive.homMonoid C _ _ P.obj Q.obj
  zero_comp _ _ _ _ := Presemiadditive.zero_comp ..
  add_comp _ _ _ _ _ _ := add_comp ..
  comp_zero _ _ _ _ := Presemiadditive.comp_zero ..
  comp_add _ _ _ _ _ _ := comp_add ..

instance (X : C) : AddCommMonoid (End X) := inferInstanceAs (AddCommMonoid (X ⟶ X))

/-- Composition by a fixed left argument as a group homomorphism -/
def leftComp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) where
  toFun g := f ≫ g
  map_zero' := Presemiadditive.comp_zero ..
  map_add' _ _ := Presemiadditive.comp_add ..

/-- Composition by a fixed right argument as a group homomorphism -/
def rightComp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) where
  toFun f := f ≫ g
  map_zero' := Presemiadditive.zero_comp ..
  map_add' _ _ := Presemiadditive.add_comp ..

variable {P Q R : C} (f f' : P ⟶ Q) (g g' : Q ⟶ R)

/-- Composition as a bilinear group homomorphism -/
def compHom : (P ⟶ Q) →+ (Q ⟶ R) →+ (P ⟶ R) where
  toFun f := leftComp _ f
  map_zero' := AddMonoidHom.ext fun _ ↦ Presemiadditive.zero_comp ..
  map_add' _ _ := AddMonoidHom.ext fun _ ↦ Presemiadditive.add_comp ..

theorem nsmul_comp (n : ℕ) : (n • f) ≫ g = n • f ≫ g :=
  map_nsmul (rightComp P g) n f

theorem comp_nsmul (n : ℕ) : f ≫ (n • g) = n • f ≫ g :=
  map_nsmul (leftComp R f) n g

@[reassoc]
theorem comp_sum {P Q R : C} {J : Type*} (s : Finset J) (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
    (f ≫ ∑ j ∈ s, g j) = ∑ j ∈ s, f ≫ g j :=
  map_sum (leftComp R f) _ _

@[reassoc]
theorem sum_comp {P Q R : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
    (∑ j ∈ s, f j) ≫ g = ∑ j ∈ s, f j ≫ g :=
  map_sum (rightComp P g) _ _

@[reassoc]
theorem sum_comp' {P Q R S : C} {J : Type*} (s : Finset J) (f : J → (P ⟶ Q)) (g : J → (Q ⟶ R))
    (h : R ⟶ S) : (∑ j ∈ s, f j ≫ g j) ≫ h = ∑ j ∈ s, f j ≫ g j ≫ h := by
  simp only [← Category.assoc]
  apply sum_comp

instance (priority := 100) preadditiveHasZeroMorphisms : HasZeroMorphisms C where
  zero := inferInstance
  comp_zero f R := show leftComp R f 0 = 0 from map_zero _
  zero_comp P _ _ f := show rightComp P f 0 = 0 from map_zero _

/-- Porting note: adding this before the ring instance allowed moduleEndRight to find
the correct Monoid structure on End. Moved both down after preadditiveHasZeroMorphisms
to make use of them -/
instance {X : C} : Semiring (End X) :=
  { End.monoid with
    zero_mul := (HasZeroMorphisms.comp_zero · _)
    mul_zero := HasZeroMorphisms.zero_comp _
    left_distrib := fun f g h => Presemiadditive.add_comp X X X g h f
    right_distrib := fun f g h => Presemiadditive.comp_add X X X h f g }

instance moduleEndRight {X Y : C} : Module (End Y) (X ⟶ Y) where
  smul_add _ _ _ := add_comp ..
  smul_zero _ := zero_comp
  add_smul _ _ _ := comp_add ..
  zero_smul _ := comp_zero

namespace IsIso

@[simp]
theorem comp_left_eq_zero [IsIso f] : f ≫ g = 0 ↔ g = 0 := by
  rw [← IsIso.eq_inv_comp, Limits.comp_zero]

@[simp]
theorem comp_right_eq_zero [IsIso g] : f ≫ g = 0 ↔ f = 0 := by
  rw [← IsIso.eq_comp_inv, Limits.zero_comp]

end IsIso

open ZeroObject

end Presemiadditive

end CategoryTheory
