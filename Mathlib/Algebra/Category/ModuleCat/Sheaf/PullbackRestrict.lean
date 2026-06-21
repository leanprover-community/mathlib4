/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Pullback commutes with restriction

In this file, we provide a natural isomorphism `PullbackRestrictIso` that shows that pullback
for sheaves of modules commutes with restriction, where restriction is the functor
`SheavesOfModules S ⥤ SheavesOfModules (Over X)` defined by pushforward along `(Over X).forget`.

-/

@[expose]
public section

universe u v₁ u₁ v₂ u₂ w

open CategoryTheory Limits

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace SheafOfModules

variable [HasBinaryProducts C] [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  [F.PreservesOneHypercovers J K] [Limits.PreservesLimitsOfShape (Discrete WalkingPair) F]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (M : SheafOfModules.{u} S)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) (X : C)

/-- This is the restriction of `φ` to `Over X`. -/
abbrev StructureHomOver :
    S.over X ⟶ ((Over.post F).sheafPushforwardContinuous _ _ _).obj (R.over (F.obj X)) :=
  (J.overPullback RingCat X).map φ

attribute [local simp] prodComparison_natural in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Natural isomorphism between `Over.star X ⋙ Over.post F` and `F ⋙ Over.star (F.obj X)` -/
abbrev Over.starCompPostNatIso : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X) :=
  NatIso.ofComponents (fun Y => Over.isoMk (asIso (prodComparison F X Y)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pushforward from `Over F(X)` to `D` composed with pushforward from `D` to `C`
is naturally isomorphic to pushforward from `Over F(X)` to `Over X` composed with
pushforward from `Over X` to `C`. -/
def pushforwardPushforwardOverNatIso : pushforward (pushforwardOver (F.obj X)) ⋙ pushforward φ ≅
    pushforward (StructureHomOver φ X) ⋙ pushforward (pushforwardOver X) := by
  haveI := F.isContinuous_comp (Over.star (F.obj X)) J K (K.over _)
  haveI := (Over.star X).isContinuous_comp (Over.post F) J (J.over X) (K.over _)
  refine pushforwardComp φ (pushforwardOver (F.obj X)) ≪≫ pushforwardCongr ?_ ≪≫
    (pushforwardNatIso _ (Over.starCompPostNatIso X).symm).symm ≪≫
    (pushforwardComp (pushforwardOver X) (StructureHomOver φ X)).symm
  ext : 3
  simp [pushforwardOver]
  congr
  simp [← Functor.map_comp, ← op_comp, prodComparison_snd]

variable [(pushforward.{u} φ).IsRightAdjoint] [(pushforward (StructureHomOver φ X)).IsRightAdjoint]

/-- Restricting from `C` to `Over X` composed with pullback from `Over X` to `Over F(X)` is
naturally isomorphic to pullback from `C` to `D` composed with restriction to `Over F(X)`. -/
def PullbackRestrictIso : pushforward.{u} (𝟙 (S.over X)) ⋙ pullback (StructureHomOver φ X) ≅
    pullback φ ⋙ pushforward.{u} (𝟙 (R.over (F.obj X))) :=
  ((overPushforwardOverAdj X).comp (pullbackPushforwardAdjunction _)).leftAdjointUniq
    (((pullbackPushforwardAdjunction φ).comp (overPushforwardOverAdj (F.obj X))).ofNatIsoRight
      (pushforwardPushforwardOverNatIso φ X))

/-- PullbackRestrict applied to `M`. -/
abbrev overPullbackIso : (pullback (StructureHomOver φ X)).obj (M.over X) ≅
    ((pullback φ).obj M).over (F.obj X) := (PullbackRestrictIso φ X).app M

end SheafOfModules
