/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Data.SetLike.SMul

/-!
# Distributive actions by submonoids
-/

namespace Submonoid

variable {M α : Type*} [Monoid M]

variable {S : Type*} [SetLike S M] (s : S) [SubmonoidClass S M]

instance distribMulAction [AddMonoid α] [DistribMulAction M α] : DistribMulAction s α where
  smul_zero r := smul_zero (r : M)
  smul_add r := smul_add (r : M)

instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] : MulDistribMulAction s α where
  smul_mul r := smul_mul' (r : M)
  smul_one r := smul_one (r : M)

end Submonoid
