/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory

#align_import algebra.category.Group.abelian from "leanprover-community/mathlib"@"f7baecbb54bd0f24f228576f97b1752fc3c9b318"

/-!
# The category of abelian groups is abelian
-/

open CategoryTheory Limits

universe u

noncomputable section

namespace AddCommGrp

variable {X Y Z : AddCommGrp.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- In the category of abelian groups, every monomorphism is normal. -/
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).inv <|
    ModuleCat.normalMono _ inferInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.normal_mono AddCommGrp.normalMono

/-- In the category of abelian groups, every epimorphism is normal. -/
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrp.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance
set_option linter.uppercaseLean3 false in
#align AddCommGroup.normal_epi AddCommGrp.normalEpi

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGrp.{u} where
  has_finite_products := ⟨HasFiniteProducts.out⟩
  normalMonoOfMono := normalMono
  normalEpiOfEpi := normalEpi

end AddCommGrp
