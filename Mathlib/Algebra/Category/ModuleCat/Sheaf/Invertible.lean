/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# Invertible sheaves of modules

A locally free sheaf of rank one has a tensor inverse given by its internal hom into the unit.
More generally, its internal hom evaluation is an isomorphism at every target.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace SheafOfModulesOfCommRing

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(W R).IsMonoidal] [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] (F : SheafOfModulesOfCommRing.{u} R)
  [F.IsLocallyFreeOfRank 1]

set_option backward.isDefEq.respectTransparency false in
/-- Internal hom evaluation for a locally free sheaf of rank one is an isomorphism. -/
instance isIso_ihom_ev_app_of_isLocallyFreeOfRank_one (G : SheafOfModulesOfCommRing.{u} R) :
    IsIso ((ihom.ev F).app G) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFreeOfRank.exists_isLocallyFreeDataOfRank
    (M := F) (n := 1)
  rw [isIso_ihom_ev_app_iff]
  apply J.W_of_isIso_of_coversTop q.coversTop
  intro i Y f
  let e : F.val.over (q.X i) ≅ 𝟙_ _ := (SheafOfModules.forget _).mapIso (q.isoUnit i)
  have : IsIso (((ihom.ev F.val).app G.val).overHom (q.X i)) := by
    rw [PresheafOfModulesOfCommRing.overHom_ihom_ev, isIso_comp_left_iff,
      MonoidalClosed.isIso_ihom_ev_app_iff_of_iso e]
    infer_instance
  exact inferInstanceAs (IsIso (((PresheafOfModules.toPresheaf _).map
    (((ihom.ev F.val).app G.val).overHom (q.X i))).app
      (op (Over.mk f))))

end SheafOfModulesOfCommRing
