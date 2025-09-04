/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonoid objects in a cartesian monoidal category.

The category of comonoid objects in a cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits Comon_Class

universe v u

noncomputable section

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom rightUnitor_hom

/--
The functor from a cartesian monoidal category to comonoids in that category,
equipping every object with the diagonal map as a comultiplication.
-/
def cartesianComon_ : C ⥤ Comon_ C where
  obj X := {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f

variable {C}

@[simp] theorem counit_eq_toUnit (A : C) [Comon_Class A] : ε[A] = toUnit _ := by ext

@[simp] theorem comul_eq_lift (A : C) [Comon_Class A] : Δ[A] = lift (𝟙 _) (𝟙 _) := by
  ext
  · simpa using comul_counit A =≫ fst _ _
  · simpa using counit_comul A =≫ snd _ _

/--
Every comonoid object in a cartesian monoidal category is equivalent to
the canonical comonoid structure on the underlying object.
-/
@[simps] def iso_cartesianComon_ (A : Comon_ C) : A ≅ (cartesianComon_ C).obj A.X :=
  { hom := .mk' (𝟙 _)
    inv := .mk' (𝟙 _) }

/--
The category of comonoid objects in a cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/
@[simps] def comonEquiv : Comon_ C ≌ C where
  functor := Comon_.forget C
  inverse := cartesianComon_ C
  unitIso := NatIso.ofComponents (fun A => iso_cartesianComon_ A)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
