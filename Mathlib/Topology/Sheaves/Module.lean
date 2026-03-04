/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Specialized results for sheaf of modules over topological spaces -/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{v})

/-- Sheaves of modules over `R.over U` are equivalent to sheaves of modules over `R |_ U`. -/
def sheafOfModulesEquivOver :
    SheafOfModules.{w} (R.over U) ≌ SheafOfModules.{w} (U.sheafRestrict.obj R) := by
  refine SheafOfModules.pushforwardPushforwardEquivalence (eqv := U.overEquivalence.symm)
    (U.overPullbackSheafEquivOver.app _).inv (U.sheafRestrictSheafEquivOver.app _).inv rfl ?_
  ext : 2
  dsimp [sheafRestrictSheafEquivOver, Iso.isoCompInverse, -sheafRestrict_obj_val_map]
  simp only [Category.id_comp, Category.assoc, ← NatTrans.naturality]
  dsimp
  rw [← R.val.map_comp_assoc, eqToHom_map]
  simp [← NatTrans.comp_app, ← Sheaf.comp_val]

/-- `sheafOfModulesEquivOver` takes `R.over U` to `R |_ U`. -/
def sheafOfModulesEquivOverUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ := .refl _

/-- `sheafOfModulesEquivOver.inverse` takes `R |_ U` to `R.over U`. -/
def sheafOfModulesEquivOverInverseUnit (R : X.Sheaf RingCat.{u}) :
    (U.sheafOfModulesEquivOver R).inverse.obj (SheafOfModules.unit.{u} _) ≅
      SheafOfModules.unit.{u} _ :=
  (U.sheafOfModulesEquivOver R).inverse.mapIso (U.sheafOfModulesEquivOverUnit R).symm ≪≫
    ((U.sheafOfModulesEquivOver R).unitIso.app _).symm

end TopologicalSpace.Opens
