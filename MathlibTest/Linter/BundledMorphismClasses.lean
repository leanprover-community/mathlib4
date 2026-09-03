module

import Mathlib.Tactic.Linter.BundledMorphismClasses
import Mathlib.Algebra.Module.LinearMap.Defs

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {F : Type*} [FunLike F M N] [LinearMapClass F R M N]

-- A definition taking in a linear map: all is fine.
def LinearMap.foo (_f : M →ₗ[R] N) : ℕ := 37

-- A definition taking in a LinearMapClass argument is not.
def LinearMap.bar (_f : F) : ℕ := 37
