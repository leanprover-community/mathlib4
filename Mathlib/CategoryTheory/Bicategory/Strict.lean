/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Bicategory.Basic

#align_import category_theory.bicategory.strict from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Strict bicategories

A bicategory is called `Strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.

## Implementation notes

In the literature of category theory, a strict bicategory (usually called a strict 2-category) is
often defined as a bicategory whose left unitors, right unitors, and associators are identities.
We cannot use this definition directly here since the types of 2-morphisms depend on 1-morphisms.
For this reason, we use `eqToIso`, which gives isomorphisms from equalities, instead of
identities.
-/


namespace CategoryTheory

open Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

/-- A bicategory is called `Strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.
-/
class Bicategory.Strict : Prop where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f := by aesop_cat
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f := by aesop_cat
  /-- Composition in a bicategory is associative. -/
  assoc : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    aesop_cat
  /-- The left unitors are given by equalities -/
  leftUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), λ_ f = eqToIso (id_comp f) := by aesop_cat
  /-- The right unitors are given by equalities -/
  rightUnitor_eqToIso : ∀ {a b : B} (f : a ⟶ b), ρ_ f = eqToIso (comp_id f) := by aesop_cat
  /-- The associators are given by equalities -/
  associator_eqToIso :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), α_ f g h = eqToIso (assoc f g h) := by
    aesop_cat
#align category_theory.bicategory.strict CategoryTheory.Bicategory.Strict

-- porting note: not adding simp to:
-- Bicategory.Strict.id_comp
-- Bicategory.Strict.comp_id
-- Bicategory.Strict.assoc
attribute [simp]
   Bicategory.Strict.leftUnitor_eqToIso
   Bicategory.Strict.rightUnitor_eqToIso
   Bicategory.Strict.associator_eqToIso

-- see Note [lower instance priority]
/-- Category structure on a strict bicategory -/
instance (priority := 100) StrictBicategory.category [Bicategory.Strict B] : Category B
    where
  id_comp := Bicategory.Strict.id_comp
  comp_id := Bicategory.Strict.comp_id
  assoc := Bicategory.Strict.assoc
#align category_theory.strict_bicategory.category CategoryTheory.StrictBicategory.category

namespace Bicategory

variable {B}

@[simp]
theorem whiskerLeft_eqToHom {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g = h) :
    f ◁ eqToHom η = eqToHom (congr_arg₂ (· ≫ ·) rfl η) := by
  cases η
  simp only [whiskerLeft_id, eqToHom_refl]
#align category_theory.bicategory.whisker_left_eq_to_hom CategoryTheory.Bicategory.whiskerLeft_eqToHom

@[simp]
theorem eqToHom_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f = g) (h : b ⟶ c) :
    eqToHom η ▷ h = eqToHom (congr_arg₂ (· ≫ ·) η rfl) := by
  cases η
  simp only [id_whiskerRight, eqToHom_refl]
#align category_theory.bicategory.eq_to_hom_whisker_right CategoryTheory.Bicategory.eqToHom_whiskerRight

end Bicategory

end CategoryTheory
