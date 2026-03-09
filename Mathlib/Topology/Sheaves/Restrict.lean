/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.Topology.Sheaves.Functors

/-!
# Restriction to open functor

Restrict to open.
-/

@[expose] public section

universe u

variable {X : TopCat.{u}}

open TopologicalSpace CategoryTheory Topology Opposite

variable (C : Type*) [Category* C] {X : TopCat.{u}} {Y : TopCat.{u}} {f : Y ⟶ X}
  (hf : IsOpenEmbedding f)

namespace TopCat.Sheaf

abbrev restrict : Sheaf C X ⥤ Sheaf C Y := by
  haveI := hf.functor_isContinuous
  exact hf.functor.sheafPushforwardContinuous C ..

abbrev restrictPushforwardAdjunction : restrict C hf ⊣ pushforward C f := by
  haveI := hf.functor_isContinuous
  exact Adjunction.sheafPushforwardContinuous hf.isOpenMap.adjunction ..

variable (F : Sheaf C X) (U V : Opens X)

abbrev toRestrict := (restrictPushforwardAdjunction C U.isOpenEmbedding).unit

lemma toRestrict_obj_obj_obj :
    ((restrict C U.isOpenEmbedding ⋙ pushforward C U.inclusion').obj F).obj.obj (op V) =
    F.obj.obj (op (U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V))) := rfl

lemma func_inc : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = U ⊓ V := by aesop

lemma toRestrict_app_hom_app : ((toRestrict C U).app F).hom.app (op V) =
    F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op := by simp

end TopCat.Sheaf
