/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Limits and colimits indexed by preorders

In this file, we obtain the following very basic results
about limits and colimits indexed by a preordered type `J`:
* a least element in `J` implies the existence of all limits indexed by `J`
* a greatest element in `J` implies the existence of all colimits indexed by `J`

-/

public section

universe v v' u u' w

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] (J : Type w) [Preorder J]

namespace Preorder

section OrderBot

instance [OrderBot J] : HasLimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

instance [Nonempty J] [Subsingleton J] : HasLimitsOfShape J C :=
  have : OrderBot J := { bot := Classical.arbitrary _, bot_le _ := by simp }
  inferInstance

end OrderBot

section OrderTop

instance [OrderTop J] : HasColimitsOfShape J C := ⟨fun _ ↦ by infer_instance⟩

instance [Nonempty J] [Subsingleton J] : HasColimitsOfShape J C :=
  have : OrderTop J := { top := Classical.arbitrary _, le_top _ := by simp }
  inferInstance

end OrderTop

end Preorder

variable {J C : Type*} [Category* J] [Category* C] {α : Type*} [Preorder α]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
noncomputable
def CategoryTheory.Limits.whiskeringColimIsoOfSubsingleton (D : α ⥤ J) [Nonempty α]
    [Subsingleton α] (a : α) :
    (Functor.whiskeringLeft α J C).obj D ⋙ colim ≅ (evaluation J C).obj (D.obj a) := by
  letI : OrderTop α := { top := a, le_top := by simp }
  refine NatIso.ofComponents
    (fun K ↦ ((colimitOfDiagramTerminal isTerminalTop _).coconePointUniqueUpToIso
      (colimit.isColimit _)).symm) fun _ ↦ colimit.hom_ext fun _ ↦ ?_
  simp [← NatTrans.naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma CategoryTheory.Limits.ι_whiskeringColimIsoOfSubsingleton_hom (D : α ⥤ J) [Nonempty α]
    [Subsingleton α] (F : J ⥤ C) (a : α) :
    dsimp% colimit.ι (D ⋙ F) a ≫ ((whiskeringColimIsoOfSubsingleton D a).app F).hom = 𝟙 _ := by
  letI : OrderTop α := { top := a, le_top := by simp }
  simp [whiskeringColimIsoOfSubsingleton, show isTerminalTop.from a = 𝟙 _ from rfl]
