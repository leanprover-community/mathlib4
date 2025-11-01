/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonoid objects in a Cartesian monoidal category.

The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits ComonObj

universe v u

noncomputable section

namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

attribute [local simp] leftUnitor_hom rightUnitor_hom

/--
The functor from a Cartesian monoidal category to comonoids in that category,
equipping every object with the diagonal map as a comultiplication.
-/
def cartesianComon : C ⥤ Comon C where
  obj X := {
    X := X
    comon := {
      comul := lift (𝟙 _) (𝟙 _)
      counit := toUnit _
    }
  }
  map f := .mk' f

@[deprecated (since := "2025-09-15")] alias cartesianComon_ := cartesianComon

variable {C}

@[simp] theorem counit_eq_toUnit (A : C) [ComonObj A] : ε[A] = toUnit _ := by ext

@[deprecated (since := "2025-05-09")] alias counit_eq_from := counit_eq_toUnit

@[simp] theorem comul_eq_lift (A : C) [ComonObj A] : Δ[A] = lift (𝟙 _) (𝟙 _) := by
  ext
  · simpa using comul_counit A =≫ fst _ _
  · simpa using counit_comul A =≫ snd _ _

@[deprecated (since := "2025-05-09")] alias comul_eq_diag := comul_eq_lift

/--
Every comonoid object in a Cartesian monoidal category is equivalent to
the canonical comonoid structure on the underlying object.
-/
@[simps] def isoCartesianComon (A : Comon C) : A ≅ (cartesianComon C).obj A.X :=
  { hom := .mk' (𝟙 _)
    inv := .mk' (𝟙 _) }

@[deprecated (since := "2025-09-15")] alias iso_cartesianComon_ := isoCartesianComon

/--
The category of comonoid objects in a Cartesian monoidal category is equivalent
to the category itself, via the forgetful functor.
-/
@[simps] def comonEquiv : Comon C ≌ C where
  functor := Comon.forget C
  inverse := cartesianComon C
  unitIso := NatIso.ofComponents isoCartesianComon
  counitIso := NatIso.ofComponents (fun _ => .refl _)

end CategoryTheory
