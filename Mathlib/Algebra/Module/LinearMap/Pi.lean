/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/

import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.Prod

/-!
# Point evaluation is linear map

Note that these results use `IsLinearMap`, which is mostly discouraged.

## Tags
linear algebra, vector space, module

-/

variable {R : Type*} {M N : Type*} {ι : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

namespace IsLinearMap

@[fun_prop]
theorem isLinearMap_pi {f : M → ι → N}
    (hf : ∀ i, IsLinearMap R (f · i)) :
    IsLinearMap R (fun x i ↦ f x i) := by
  apply IsLinearMap.mk
  · intro x y; funext i
    simp [(hf i).1]
  · intro x y; funext i
    simp [(hf i).2]

@[fun_prop]
theorem isLinearMap_apply {i : ι} :
    IsLinearMap R fun f : ι → M => f i := by
  apply IsLinearMap.mk <;> simp


#check fun (x : M) ↦ₗ[R] 3 • x + x

end IsLinearMap
