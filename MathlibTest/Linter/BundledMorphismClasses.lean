module

public import Mathlib.Tactic.Linter.BundledMorphismClasses
public import Mathlib.Algebra.Module.LinearMap.Defs

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  {F : Type*} [FunLike F M N] [LinearMapClass F R M N]

section definitions

-- A definition taking in a linear map: all is fine.
def LinearMap.foo (_f : M →ₗ[R] N) : ℕ := 37

-- A definition taking in a LinearMapClass argument is not.

-- Note: the linter does not fire here, because the typeclass assumption is not actually used.
-- A hacky approach (such as looking at the printed type) could have false positives here.
def LinearMap.bar (_f : F) : ℕ := 37

-- Heuristic: we don't warn on definitions `FooHom.ofClass` or `FooHomClass.toFooHom`.
-- (The latter should be renamed to the former, but we should not give a misleading error
-- until this is complete.)
def LinearMapFoo.ofClass (f : F) : M →ₗ[R] N := LinearMap.ofClass f

def LinearMapClass.toLinearMap (f : F) : M →ₗ[R] N := LinearMap.ofClass f

-- We also exclude deprecated declarations.
@[deprecated LinearMap.bar (since := "2026-09-07")]
def LinearMapFoo.bar' (f : F) : M →ₗ[R] N := LinearMap.ofClass f

-- The linter does not fire on instances either.
set_option linter.overlappingInstances false in
instance [_h: LinearMapClass F R M N] : FunLike F M N := by infer_instance

set_option linter.overlappingInstances false in
instance [h : SemilinearMapClass F (RingHom.id R) M N] : LinearMapClass F R M N := h

-- But the linter fires on this declaration.
def LinearMap.baz (f : F) : M →ₗ[R] N := f

/--
error: -- Found 2 errors in 8 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `defsWithMorphismClass` linter reports:
FOUND definitions with a bundled morphism argument.
This linter can be disabled with `@[nolint defsWithMorphismClass]`. -/
#check @LinearMapClass.toLinearMap /- The definition `LinearMapClass.toLinearMap` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
#check @LinearMap.baz /- The definition `LinearMap.baz` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
-/
#guard_msgs in
#lint only defsWithMorphismClass

-- Another bad example, involving a different morphism class.
def bar {S F : Type*} [Semiring S] [Module S N] {σ : R →+* S}
    [FunLike F M N] [SemilinearMapClass F σ M N] (f : F) : M →ₛₗ[σ] N := f

/--
error: -- Found 3 errors in 9 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `defsWithMorphismClass` linter reports:
FOUND definitions with a bundled morphism argument.
This linter can be disabled with `@[nolint defsWithMorphismClass]`. -/
#check @LinearMapClass.toLinearMap /- The definition `LinearMapClass.toLinearMap` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
#check @LinearMap.baz /- The definition `LinearMap.baz` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
#check @bar /- The definition `bar` takes a `SemilinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `SemilinearMap` argument instead. -/
-/
#guard_msgs in
#lint only defsWithMorphismClass

end definitions

section theorems

-- We don't lint on deprecated theorems.
@[deprecated "test-only; deprecated forever" (since := "9999-12-31")]
lemma foolem' {f : F} : LinearMap.baz (R := R) f = f := sorry

-- This errors: LinearMap.baz is a definition in terms of a morphism class,
-- so this lemma should be stated for a linear map.
lemma foolem {f : F} : LinearMap.baz (R := R) f = f := sorry

-- This version is better.
lemma foolem_fixed {f : M →ₗ[R] N} : LinearMap.baz (R := R) f = f := sorry

/--
error: -- Found 4 errors in 12 declarations (plus 0 automatically generated ones) in the current file with 1 linters

/- The `defsWithMorphismClass` linter reports:
FOUND definitions with a bundled morphism argument.
This linter can be disabled with `@[nolint defsWithMorphismClass]`. -/
#check @LinearMapClass.toLinearMap /- The definition `LinearMapClass.toLinearMap` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
#check @LinearMap.baz /- The definition `LinearMap.baz` takes a `LinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `LinearMap` argument instead. -/
#check @bar /- The definition `bar` takes a `SemilinearMapClass` argument.
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the definition to take in a `SemilinearMap` argument instead. -/
#check @foolem /- The theorem `foolem` involves a definition on a bundled morphism
(namely `TODO`), but takes in the morphism class `LinearMapClass` as argument:
Per https://github.com/leanprover-community/mathlib4/issues/31365, this is a bad idea:
please change the theorem to reference a concrete `LinearMap` instead. -/
-/
#guard_msgs in
#lint only defsWithMorphismClass

end theorems
