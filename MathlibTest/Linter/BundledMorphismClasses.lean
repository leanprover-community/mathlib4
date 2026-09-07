module

public import Mathlib.Tactic.Linter.BundledMorphismClasses
public import Mathlib.Algebra.Module.LinearMap.Defs

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {F : Type*} [FunLike F M N] [LinearMapClass F R M N]

-- A definition taking in a linear map: all is fine.
def LinearMap.foo (_f : M →ₗ[R] N) : ℕ := 37

-- A definition taking in a LinearMapClass argument is not.

-- Note: the linter does not fire here, because the typeclass assumption is not actually used.
-- A hacky approach (such as looking at the printed type) could have false positives here.
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
please change the definition to take in a `LinearMap` argument instead. -/
-/
#guard_msgs in
#lint only defsWithMorphismClass

-- Another bad example, involving a different morphism class.
def bar {S F : Type*} [Semiring S] [Module S N] {σ : R →+* S}
    [FunLike F M N] [SemilinearMapClass F σ M N] (f : F) : M →ₛₗ[σ] N := f

/--
error: -- Found 2 errors in 4 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `defsWithMorphismClass` linter reports:
FOUND definitions with a bundled morphism argument.
This linter can be disabled with `@[nolint defsWithMorphismClass]`. -/
#check @LinearMap.baz /- The definition `LinearMap.baz` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is (usually) a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
#check @bar /- The definition `bar` takes a `SemilinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is (usually) a bad idea:
please change the definition to take in a `SemilinearMap` argument instead. -/
-/
#guard_msgs in
#lint only defsWithMorphismClass
