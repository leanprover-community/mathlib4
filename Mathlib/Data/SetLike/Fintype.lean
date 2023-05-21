/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.set_like.fintype
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Set-like fintype

This file contains a fintype instance for set-like objects such as subgroups. If `SetLike A B`
and `Fintype B` then `Fintype A`.
-/


namespace SetLike

/-- TODO: It should be possible to obtain a computable version of this for most
SetLike objects. If we add those instances, we should remove this one. -/
noncomputable instance (priority := 100) {A B : Type _} [SetLike A B] [Fintype B] : Fintype A :=
  Fintype.ofInjective SetLike.coe SetLike.coe_injective

-- See note [lower instance priority]
instance (priority := 100) {A B : Type _} [SetLike A B] [Finite B] : Finite A :=
  Finite.of_injective SetLike.coe SetLike.coe_injective

end SetLike
