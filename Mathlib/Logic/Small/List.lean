/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module logic.small.list
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Small.Basic
import Mathbin.Data.Vector.Basic

/-!
# Instances for `small (list α)` and `small (vector α)`.

These must not be in `logic.small.basic` as this is very low in the import hierarchy,
and is used by category theory files which do not need everything imported by `data.vector.basic`.
-/


universe u v

instance small_vector {α : Type v} {n : ℕ} [Small.{u} α] : Small.{u} (Vector α n) :=
  small_of_injective (Equiv.vectorEquivFin α n).Injective
#align small_vector small_vector

instance small_list {α : Type v} [Small.{u} α] : Small.{u} (List α) :=
  by
  let e : (Σn, Vector α n) ≃ List α := Equiv.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective
#align small_list small_list

