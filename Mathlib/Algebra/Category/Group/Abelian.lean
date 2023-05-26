/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module algebra.category.Group.abelian
! leanprover-community/mathlib commit f7baecbb54bd0f24f228576f97b1752fc3c9b318
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Category.Group.ZModuleEquivalence
import Mathbin.Algebra.Category.Group.Limits
import Mathbin.Algebra.Category.Group.Colimits
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.CategoryTheory.Abelian.Basic

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
def normalMono (hf : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
#align AddCommGroup.normal_mono AddCommGroupCat.normalMono

/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (hf : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGroupCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
#align AddCommGroup.normal_epi AddCommGroupCat.normalEpi

end

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGroupCat.{u}
    where
  HasFiniteProducts := ⟨by infer_instance⟩
  normalMonoOfMono X Y := normalMono
  normalEpiOfEpi X Y := normalEpi
  add_comp := by
    intros
    simp only [preadditive.add_comp]
  comp_add := by
    intros
    simp only [preadditive.comp_add]

end AddCommGroupCat

