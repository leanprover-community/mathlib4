/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno

! This file was ported from Lean 3 source module category_theory.bicategory.strict
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EqToHom
import Mathbin.CategoryTheory.Bicategory.Basic

/-!
# Strict bicategories

A bicategory is called `strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.

## Implementation notes

In the literature of category theory, a strict bicategory (usually called a strict 2-category) is
often defined as a bicategory whose left unitors, right unitors, and associators are identities.
We cannot use this definition directly here since the types of 2-morphisms depend on 1-morphisms.
For this reason, we use `eq_to_iso`, which gives isomorphisms from equalities, instead of
identities.
-/


namespace CategoryTheory

open Bicategory

universe w v u

variable (B : Type u) [Bicategory.{w, v} B]

/-- A bicategory is called `strict` if the left unitors, the right unitors, and the associators are
isomorphisms given by equalities.
-/
class Bicategory.Strict : Prop where
  id_comp' : ∀ {a b : B} (f : a ⟶ b), 𝟙 a ≫ f = f := by obviously
  comp_id' : ∀ {a b : B} (f : a ⟶ b), f ≫ 𝟙 b = f := by obviously
  assoc' : ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    obviously
  leftUnitor_eq_to_iso' : ∀ {a b : B} (f : a ⟶ b), λ_ f = eqToIso (id_comp' f) := by obviously
  rightUnitor_eq_to_iso' : ∀ {a b : B} (f : a ⟶ b), ρ_ f = eqToIso (comp_id' f) := by obviously
  associator_eq_to_iso' :
    ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), α_ f g h = eqToIso (assoc' f g h) := by
    obviously
#align category_theory.bicategory.strict CategoryTheory.Bicategory.Strict

restate_axiom bicategory.strict.id_comp'

restate_axiom bicategory.strict.comp_id'

restate_axiom bicategory.strict.assoc'

restate_axiom bicategory.strict.left_unitor_eq_to_iso'

restate_axiom bicategory.strict.right_unitor_eq_to_iso'

restate_axiom bicategory.strict.associator_eq_to_iso'

attribute [simp]
  bicategory.strict.id_comp bicategory.strict.left_unitor_eq_to_iso bicategory.strict.comp_id bicategory.strict.right_unitor_eq_to_iso bicategory.strict.assoc bicategory.strict.associator_eq_to_iso

-- see Note [lower instance priority]
/-- Category structure on a strict bicategory -/
instance (priority := 100) StrictBicategory.category [Bicategory.Strict B] : Category B
    where
  id_comp' a b := Bicategory.Strict.id_comp
  comp_id' a b := Bicategory.Strict.comp_id
  assoc' a b c d := Bicategory.Strict.assoc
#align category_theory.strict_bicategory.category CategoryTheory.StrictBicategory.category

namespace Bicategory

variable {B}

@[simp]
theorem whiskerLeft_eqToHom {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g = h) :
    f ◁ eqToHom η = eqToHom (congr_arg₂ (· ≫ ·) rfl η) :=
  by
  cases η
  simp only [whisker_left_id, eq_to_hom_refl]
#align category_theory.bicategory.whisker_left_eq_to_hom CategoryTheory.Bicategory.whiskerLeft_eqToHom

@[simp]
theorem eqToHom_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f = g) (h : b ⟶ c) :
    eqToHom η ▷ h = eqToHom (congr_arg₂ (· ≫ ·) η rfl) :=
  by
  cases η
  simp only [id_whisker_right, eq_to_hom_refl]
#align category_theory.bicategory.eq_to_hom_whisker_right CategoryTheory.Bicategory.eqToHom_whiskerRight

end Bicategory

end CategoryTheory

