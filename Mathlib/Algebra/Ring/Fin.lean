/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Logic.Equiv.Fin

#align_import algebra.ring.fin from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Rings and `Fin`

This file collects some basic results involving rings and the `Fin` type

## Main results

 * `RingEquiv.piFinTwo`: The product over `Fin 2` of some rings is the cartesian product

-/


/-- The product over `Fin 2` of some rings is just the cartesian product of these rings. -/
@[simps]
def RingEquiv.piFinTwo (R : Fin 2 → Type*) [∀ i, Semiring (R i)] :
    (∀ i : Fin 2, R i) ≃+* R 0 × R 1 :=
  { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }
#align ring_equiv.pi_fin_two RingEquiv.piFinTwo
#align ring_equiv.pi_fin_two_apply RingEquiv.piFinTwo_apply
#align ring_equiv.pi_fin_two_symm_apply RingEquiv.piFinTwo_symm_apply
