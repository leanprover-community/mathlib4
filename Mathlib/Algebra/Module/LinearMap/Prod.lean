/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/

import Mathlib.Algebra.Module.Prod
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Addition and subtraction are linear maps from the product space

Note that these results use `IsLinearMap`, which is mostly discouraged.

## Tags
linear algebra, vector space, module

-/

variable {R : Type*} {M : Type*} [Semiring R]

namespace IsLinearMap

theorem isLinearMap_add [AddCommMonoid M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 + x.2 := by
  apply IsLinearMap.mk
  · intro x y
    simp only [Prod.fst_add, Prod.snd_add]
    abel
  · simp [smul_add]

theorem isLinearMap_sub [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · simp [smul_sub]

end IsLinearMap
