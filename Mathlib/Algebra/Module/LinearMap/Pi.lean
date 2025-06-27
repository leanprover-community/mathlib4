/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Mathlib.LinearAlgebra.Pi

/-!
# Point evaluation is linear map

Note that these results use `IsLinearMap`, which is mostly discouraged.

## Tags
linear algebra, vector space, module

-/


namespace IsLinearMap

variable {R : Type*} {M N : Type*} {ι : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

@[fun_prop]
theorem isLinearMap_pi {f : M → ι → N}
    (hf : ∀ i, IsLinearMap R (f · i)) :
    IsLinearMap R (fun x i ↦ f x i) :=
  (LinearMap.pi (fun i => (hf i).mk')).isLinear

@[fun_prop]
theorem isLinearMap_apply {i : ι} :
    IsLinearMap R fun f : ι → M => f i :=
  (LinearMap.proj _).isLinear

end IsLinearMap


namespace LinearMap

variable {R : Type*} {M M₂ M₃ : Type*} [CommSemiring R]
  [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₂] [Module R M₃]

@[fun_prop]
theorem isLinearMap_apply [SMulCommClass R R M₃] (f : M → M₂ →ₗ[R] M₃) (y : M₂)
    (hf : IsLinearMap R f) :
    IsLinearMap R (fun x => f x y) :=
  (LinearMap.applyₗ y |>.comp hf.mk').isLinear

end LinearMap
