/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Logic.Small.Basic
import Mathlib.Data.Vector.Basic

#align_import logic.small.list from "leanprover-community/mathlib"@"509de852e1de55e1efa8eacfa11df0823f26f226"

/-!
# Instances for `Small (List α)` and `Small (Vector α)`.

These must not be in `Logic.Small.Basic` as this is very low in the import hierarchy,
and is used by category theory files which do not need everything imported by `Data.Vector.Basic`.
-/


universe u v

instance smallVector {α : Type v} {n : ℕ} [Small.{u} α] : Small.{u} (Vector α n) :=
  small_of_injective (Equiv.vectorEquivFin α n).injective
#align small_vector smallVector

instance smallList {α : Type v} [Small.{u} α] : Small.{u} (List α) := by
  let e : (Σn, Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  -- ⊢ Small.{u, v} (List α)
  exact small_of_surjective e.surjective
  -- 🎉 no goals
#align small_list smallList
