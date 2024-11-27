/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# Distributive actions by submonoids
-/

namespace Submonoid
variable {M α : Type*} [Monoid M]

/-- The action by a submonoid is the action by the underlying monoid. -/
instance distribMulAction [AddMonoid α] [DistribMulAction M α] (S : Submonoid M) :
    DistribMulAction S α :=
  DistribMulAction.compHom _ S.subtype

/-- The action by a submonoid is the action by the underlying monoid. -/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] (S : Submonoid M) :
    MulDistribMulAction S α :=
  MulDistribMulAction.compHom _ S.subtype

end Submonoid
