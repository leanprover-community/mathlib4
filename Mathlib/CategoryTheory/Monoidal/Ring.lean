/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
public import Mathlib.Algebra.Ring.Basic

/-!
# Ring objects

-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [BraidedCategory C]

open scoped MonObj AddMonObj

class RingObj (R : C) extends AddGrpObj R, IsCommAddMonObj R, MonObj R where
  mul_add (R) : R ◁ σ ≫ μ = lift ((R ◁ fst _ _) ≫ μ) ((R ◁ snd _ _) ≫ μ) ≫ σ
  add_mul (R) : σ ▷ R ≫ μ = lift (fst _ _ ▷ _ ≫ μ) (snd _ _ ▷ _ ≫ μ) ≫ σ

section

variable {R : C} [RingObj R] {X : C}

lemma Hom.mul_add (a b c : X ⟶ R) : a * (b + c) = a * b + a * c := by
  have := lift a (lift b c) ≫= RingObj.mul_add R
  simp only [lift_whiskerLeft_assoc] at this
  simp only [add_def, mul_def, this, ← Category.assoc]
  congr 1
  cat_disch

lemma Hom.add_mul (a b c : X ⟶ R) : (a + b) * c = a * c + b * c := by
  have := lift (lift a b) c ≫= RingObj.add_mul R
  simp only [lift_whiskerRight_assoc] at this
  simp only [add_def, mul_def, this, ← Category.assoc]
  congr 1
  cat_disch

abbrev Hom.ring {X : C} : Ring (X ⟶ R) where
  left_distrib := Hom.mul_add
  right_distrib := Hom.add_mul
  mul_zero a := by simpa using mul_add a 0 0
  zero_mul a := by simpa using add_mul 0 0 a

scoped[CategoryTheory.MonObj] attribute [instance] Hom.ring

end

class CommRingObj (R : C) extends RingObj R, IsCommMonObj R where

abbrev Hom.commRing {R : C} {X : C} [CommRingObj R] : CommRing (X ⟶ R) where

scoped[CategoryTheory.MonObj] attribute [instance] Hom.commRing

end CategoryTheory
