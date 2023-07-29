/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.GroupCat.ZModuleEquivalence
import Mathlib.Algebra.Category.GroupCat.Limits
import Mathlib.Algebra.Category.GroupCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic

#align_import algebra.category.Group.abelian from "leanprover-community/mathlib"@"f7baecbb54bd0f24f228576f97b1752fc3c9b318"

/-!
# The category of abelian groups is abelian
-/


open CategoryTheory

open CategoryTheory.Limits

universe u

noncomputable section

namespace AddCommGroupCat

section

variable {X Y : AddCommGroupCat.{u}} (f : X ⟶ Y)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.normal_mono AddCommGroupCat.normalMono

/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.normal_epi AddCommGroupCat.normalEpi

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupCat.{u} where
  has_finite_products := ⟨by infer_instance⟩
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi
  add_comp := by
    intros
    simp only [Preadditive.add_comp]
  comp_add := by
    intros
    simp only [Preadditive.comp_add]

end AddCommGroupCat
