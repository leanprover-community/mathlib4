/-
Copyright (c) XXX. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XXX
-/

import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.RestrictScalars
/-!
# XXX
-/

section Module

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

@[simp]
theorem LinearMap.ker_restrictScalars (f : M →ₗ[S] N) :
    LinearMap.ker (f.restrictScalars R) = f.ker.restrictScalars R :=
  rfl

end Module
