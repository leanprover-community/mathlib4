module

public import Mathlib.Tactic.Linter.BundledMorphismClasses
public import Mathlib.Algebra.Module.LinearMap.Defs

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {F : Type*} [FunLike F M N] [LinearMapClass F R M N]

-- A definition taking in a linear map: all is fine.
def LinearMap.foo (_f : M →ₗ[R] N) : ℕ := 37

-- A definition taking in a LinearMapClass argument is not.

-- Note: the linter does not fire here, because the typeclass assumption is not actually used.
def LinearMap.bar (_f : F) : ℕ := 37

-- But the linter fires on this declaration.
def LinearMap.baz (f : F) : M →ₗ[R] N := f

/--
error: -- Found 1 error in 3 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `defsWithMorphismClass` linter reports:
FOUND definitions with a bundled morphism argument.
This linter can be disabled with `@[nolint defsWithMorphismClass]`. -/
#check @LinearMap.baz /- The definition `LinearMap.baz` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is (usually) a bad idea:
please change the definition to take in a `LinearMap` argument instead.
Note that this linter has false positives if a LinearMapClass is just coerced to a function.
Note: the 'proper' linter check doesn't fire here; there's still a bug to fix! -/
-/
#guard_msgs in
#lint only defsWithMorphismClass
