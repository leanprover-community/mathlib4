/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Data.SetLike.SMul
/-!
# Distributive actions by submonoids
-/

namespace Submonoid

variable {M α : Type*} [Monoid M]

variable {S : Type*} [SetLike S M] (s : S) [SubmonoidClass S M]

@[to_additive]
instance mulAction [MulAction M α] : MulAction s α where
  one_smul := one_smul M
  mul_smul r₁ r₂ := mul_smul (r₁ : M) r₂

instance distribMulAction [AddMonoid α] [DistribMulAction M α] : DistribMulAction s α where
  smul_zero r := smul_zero (r : M)
  smul_add r := smul_add (r : M)

instance mulDistribMulAction [Monoid α] [MulDistribMulAction M α] : MulDistribMulAction s α where
  smul_mul r := smul_mul' (r : M)
  smul_one r := smul_one (r : M)

end Submonoid
