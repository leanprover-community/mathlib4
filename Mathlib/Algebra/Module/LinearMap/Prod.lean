/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/

import Mathlib.LinearAlgebra.Prod

/-!
# Addition and subtraction are linear maps from the product space

Note that these results use `IsLinearMap`, which is mostly discouraged.

## Tags
linear algebra, vector space, module

-/

variable {R : Type*} {M M₂ M₃ : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid M₃] [Module R M₃]

namespace IsLinearMap

@[fun_prop]
theorem isLinearMap_prodMk {f : M → M₂} {g : M → M₃}
    (hf : IsLinearMap R f) (hg : IsLinearMap R g)  :
    IsLinearMap R fun x : M => (f x, g x) :=
  (LinearMap.prod hf.mk' hg.mk').isLinear

@[fun_prop]
theorem isLinearMap_fst {f : M → M₂×M₃} (hf : IsLinearMap R f)  :
    IsLinearMap R fun x : M => (f x).1 :=
  ((LinearMap.fst _ _ _).comp hf.mk').isLinear

@[fun_prop]
theorem isLinearMap_snd {f : M → M₂×M₃} (hf : IsLinearMap R f)  :
    IsLinearMap R fun x : M => (f x).2 :=
  ((LinearMap.snd _ _ _).comp hf.mk').isLinear

@[fun_prop]
theorem isLinearMap_add :
    IsLinearMap R fun x : M × M => x.1 + x.2 :=
  ((LinearMap.fst _ _ _) + (LinearMap.snd _ _ _)).isLinear

@[fun_prop]
theorem isLinearMap_sub {M : Type*} [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 :=
  ((LinearMap.fst R M M) - (LinearMap.snd _ _ _)).isLinear

end IsLinearMap
