/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.SetLike

/-!
# The category of abelian groups is abelian
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace AddCommGrpCat

variable {X Y Z : AddCommGrpCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- In the category of abelian groups, every monomorphism is normal. -/
@[implicit_reducible]
def normalMono (_ : Mono f) : NormalMono f :=
  equivalenceReflectsNormalMono (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalMono _ inferInstance

/-- In the category of abelian groups, every epimorphism is normal. -/
@[implicit_reducible]
def normalEpi (_ : Epi f) : NormalEpi f :=
  equivalenceReflectsNormalEpi (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).inv <|
    ModuleCat.normalEpi _ inferInstance

/-- The category of abelian groups is abelian. -/
instance : Abelian AddCommGrpCat.{u} where
  normalMonoOfMono f hf := ⟨normalMono f hf⟩
  normalEpiOfEpi f hf := ⟨normalEpi f hf⟩

end AddCommGrpCat
