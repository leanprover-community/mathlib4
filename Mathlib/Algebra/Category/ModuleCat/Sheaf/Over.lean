/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Over

-/

@[expose]
public section

universe u v₁ u₁ v₂ u₂ w

open CategoryTheory Limits

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {D : Type u₂} [Category.{v₂} D]
  [HasBinaryProducts D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (M : SheafOfModules.{u} S)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [(pushforward.{u} φ).IsRightAdjoint]

variable (X : C) [(Over.post F).IsContinuous (J.over X) (K.over (F.obj X))]

set_option backward.isDefEq.respectTransparency false in
abbrev StructureHomOver :
    S.over X ⟶ ((Over.post F).sheafPushforwardContinuous _ _ _).obj (R.over (F.obj X)) :=
  (J.overPullback RingCat X).map φ

variable [(pushforward (StructureHomOver φ X)).IsRightAdjoint] [Limits.PreservesFiniteProducts F]

attribute [local simp] prodComparison_natural in
set_option backward.isDefEq.respectTransparency false in
@[simps!]
def Over.starCompPostNatIso : Over.star X ⋙ Over.post F ≅ F ⋙ Over.star (F.obj X) :=
  NatIso.ofComponents (fun Y => Over.isoMk (asIso (prodComparison F X Y)))

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def pushforwardPushforwardOverNatIso : pushforward (pushforwardOver (F.obj X)) ⋙ pushforward φ ≅
    pushforward (StructureHomOver φ X) ⋙ pushforward (pushforwardOver X) := by
  haveI := F.isContinuous_comp (Over.star (F.obj X)) J K (K.over _)
  haveI := (Over.star X).isContinuous_comp (Over.post F) J (J.over X) (K.over _)
  refine (pushforwardComp (pushforwardOver X) (StructureHomOver φ X) ≪≫
    pushforwardNatIso _ (Over.starCompPostNatIso X).symm ≪≫ pushforwardCongr ?_ ≪≫
    (pushforwardComp φ (pushforwardOver (F.obj X))).symm).symm
  ext : 3
  simp [pushforwardOver]
  congr
  simp [IsIso.comp_inv_eq, ← Functor.map_comp, ← op_comp, prodComparison_snd]

@[simps!]
def pullbackRestrict : pushforward.{u} (𝟙 (S.over X)) ⋙ pullback (StructureHomOver φ X) ≅
    pullback φ ⋙ pushforward.{u} (𝟙 (R.over (F.obj X))) :=
  ((overPushforwardOverAdj X).comp (pullbackPushforwardAdjunction _)).leftAdjointUniq
    (((pullbackPushforwardAdjunction φ).comp (overPushforwardOverAdj (F.obj X))).ofNatIsoRight
      (pushforwardPushforwardOverNatIso φ X))

abbrev overPullback :
    (pullback (StructureHomOver φ X)).obj (M.over X) ≅
    ((pullback φ).obj M).over (F.obj X) := (pullbackRestrict φ X).app M

#check M.overPullback φ X

end SheafOfModules
