/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Distributive actions by submonoids
-/

assert_not_exists RelIso Ring

namespace Submonoid

variable {M α : Type*} [Monoid M]

variable {S : Type*} [SetLike S M] (s : S) [SubmonoidClass S M]

instance (priority := low) [AddMonoid α] [DistribMulAction M α] : DistribMulAction s α where
  smul_zero r := smul_zero (r : M)
  smul_add r := smul_add (r : M)

/-- The action by a submonoid is the action by the underlying monoid. -/
instance distribMulAction [AddMonoid α] [DistribMulAction M α] (S : Submonoid M) :
    DistribMulAction S α :=
  inferInstance

instance (priority := low) [Monoid α] [MulDistribMulAction M α] : MulDistribMulAction s α where
  smul_mul r := smul_mul' (r : M)
  smul_one r := smul_one (r : M)

/-- The action by a submonoid is the action by the underlying monoid. -/
instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] (S : Submonoid M) :
    MulDistribMulAction S α :=
  inferInstance

end Submonoid
