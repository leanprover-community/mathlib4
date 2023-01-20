/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.set_like.fintype
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Fintype.Powerset

/-!
# Set-like fintype

This file contains a fintype instance for set-like objects such as subgroups. If `set_like A B`
and `fintype B` then `fintype A`.
-/


namespace SetLike

/-- TODO: It should be possible to obtain a computable version of this for most
set_like objects. If we add those instances, we should remove this one. -/
@[nolint dangerous_instance, instance]
noncomputable instance (priority := 100) {A B : Type _} [Fintype B] [SetLike A B] : Fintype A :=
  Fintype.ofInjective coe SetLike.coe_injective

-- See note [lower instance priority]
@[nolint dangerous_instance]
instance (priority := 100) {A B : Type _} [Finite B] [SetLike A B] : Finite A :=
  Finite.of_injective coe SetLike.coe_injective

end SetLike

