/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Stonean.Basic
/-!
# Explicit (co)limits in the category of Stonean spaces

This file describes some explicit (co)limits in `Stonean`

## Overview

We define explicit finite coproducts in `Stonean` as sigma types (disjoint unions) and explicit
pullbacks where one of the maps is an open embedding

-/

universe u

open CategoryTheory Limits

attribute [local instance] ConcreteCategory.instFunLike

namespace Stonean

instance : HasFiniteCoproducts Stonean.{u} := by
  apply CompHausLike.has_finite_coproducts.{u}
  intro α _ X
  exact show ExtremallyDisconnected (Σ (a : α), X a) from inferInstance

instance : PreservesFiniteCoproducts (CompHausLike.compHausLikeToTop _ : Stonean.{u} ⥤ _) := by
  apply CompHausLike.preservesFiniteCoproducts.{u}
  intro α _ X
  exact show ExtremallyDisconnected (Σ (a : α), X a) from inferInstance

variable {X Y Z : Stonean} (f : X ⟶ Z) {i : Y ⟶ Z} (hi : OpenEmbedding i)

theorem extremallyDisconnected_preimage : ExtremallyDisconnected (f ⁻¹' (Set.range i)) where
  open_closure U hU := by
    have h : IsClopen (f ⁻¹' (Set.range i)) :=
      ⟨IsClosed.preimage f.continuous (isCompact_range i.continuous).isClosed,
        IsOpen.preimage f.continuous hi.isOpen_range⟩
    rw [← (closure U).preimage_image_eq Subtype.coe_injective,
      ← h.1.closedEmbedding_subtype_val.closure_image_eq U]
    exact isOpen_induced (ExtremallyDisconnected.open_closure _
      (h.2.openEmbedding_subtype_val.isOpenMap U hU))

theorem extremallyDisconnected_pullback :
    ExtremallyDisconnected {xy : X × Y | f xy.1 = i xy.2} :=
  have := extremallyDisconnected_preimage f hi
  extremallyDisconnected_of_homeo (TopCat.pullbackHomeoPreimage f f.2 i hi.toEmbedding).symm

instance : HasPullbacksOfInclusions Stonean.{u} := by
  apply CompHausLike.hasPullbacksOfInclusions
  · intro α _ X
    exact show ExtremallyDisconnected (Σ (a : α), X a) from inferInstance
  · intro _ _ _ _ _ hi
    exact extremallyDisconnected_pullback _ hi

noncomputable
instance : PreservesPullbacksOfInclusions
    (CompHausLike.compHausLikeToTop _ : Stonean.{u} ⥤ _) := by
  apply CompHausLike.preservesPullbacksOfInclusions
  · intro α _ X
    exact show ExtremallyDisconnected (Σ (a : α), X a) from inferInstance
  · intro _ _ _ _ _ hi
    exact extremallyDisconnected_pullback _ hi

instance : FinitaryExtensive Stonean.{u} :=
  finitaryExtensive_of_preserves_and_reflects (CompHausLike.compHausLikeToTop _ : Stonean ⥤ _)

noncomputable instance : PreservesFiniteCoproducts Stonean.toCompHaus := by
  apply CompHausLike.preservesFiniteCoproducts'
  intro α _ X
  exact show ExtremallyDisconnected (Σ (a : α), X a) from inferInstance

noncomputable instance : PreservesFiniteCoproducts Stonean.toProfinite := by
  apply CompHausLike.preservesFiniteCoproducts'
  intro α _ X
  exact show ExtremallyDisconnected (Σ (a : α), X a) from inferInstance

end Stonean
