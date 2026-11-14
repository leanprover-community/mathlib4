module

public import Mathlib.Algebra.Group.Defs
public meta import Mathlib.Lean.Exception
public import Mathlib.Tactic.ReduceModChar.Ext
public import Mathlib.Tactic.Translate.ToDifferentiable
public import Qq.MetaM

import all Init.Prelude
import all Mathlib.Tactic.Translate.Expr

open Qq Lean Meta Elab Command Mathlib Tactic Translate ToDifferentiable

public section

-- work in a namespace so that it doesn't matter if names clash
namespace Test

section inputValidation

variable {E F : Type*}

def Foo (n m : ℕ) (f : E → F) : Prop := ∀ x, f x = f x

def Bar (f : E → F) : Prop := ∀ x, f x = f x

-- Specifying an index that is too large
/-- error: index `6` is out of bounds, there are only `5` arguments -/
#guard_msgs in
attribute [to_differentiable (omit := 6) Foo1] Foo

variable {f₀ : E → F}

-- Bogus configuration: the code doesn't typecheck, so Lean complains
/--
error: `@[to_differentiable]` failed to add declaration `Foo2`.
  The translated value is not type correct.
Application type mismatch: The argument
  x
has type
  E
but is expected to have type
  ?E✝
in the application
  ?f✝ x

For help, see the docstring of `to_additive`, section `Troubleshooting`.
-/
#guard_msgs in
attribute [to_differentiable (omit := 5) Foo2] Foo

-- Specifying the same argument multiple times is just redundant (but nothing else).
attribute [to_differentiable (omit := 3 3 3) Foo3] Foo
/-- info: Test.Foo3.{u_1, u_2} {E : Type u_1} {F : Type u_2} (m : ℕ) (f : E → F) : Prop -/
#guard_msgs in
#check Foo3

set_option linter.translate.overwrite false

-- Removing multiple arguments is fine
attribute [to_differentiable (omit := 3 4) Foo4] Foo

-- Specifying an attribute multiple times again is just fine, nothing happens.
set_option linter.translate.existing false in
attribute [to_differentiable (omit := 3 4 4 3 3 4) Foo4] Foo

-- The to_additive machinery checks that the new declaration really has the same type:
-- if there is a mismatch, there is a warning.
/--
warning: The translated declaration `Foo4` already exists. Please specify this explicitly using `@[to_differentiable existing]`.

Note: This linter can be disabled with `set_option linter.translate.existing false`
---
error: `to_differentiable` validation failed: expected
  {E : Type _} → {F : Type _} → ℕ → (E → F) → Prop
but `Foo4` has type
  {E : Type u_1} → {F : Type u_2} → (E → F) → Prop
-/
#guard_msgs in
attribute [to_differentiable (omit := 3) Foo4] Foo

-- Omission arguments are treated as if they were in sorted order.
set_option linter.translate.existing false in
attribute [to_differentiable (omit := 4 3) Foo4] Foo

-- Omitting arguments together with the dual option errors. TODO can we test this? Is fine here.

-- Specifying overlapping arguments to omit and reorder errors. TODO!
attribute [to_differentiable (reorder := 3 4) (omit := 3 4) Foo4] Foo

attribute [to_differentiable (reorder := 2 4) (omit := 2 3) Foo4] Foo

end inputValidation


variable {R : Type*} [Group R] {E F : Type*} [Group E] [Group F]

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

-- Artificially simplified definitions (which hence contain unused variables).
def ContDiff (n : ℕ) (f : E → F) : Prop := True

def Differentiable (f : E → F) : Prop := True

attribute [to_differentiable existing (omit := 3) Differentiable] ContDiff

lemma ContDiff.add [Add F] (f g : E → F) (hf : ContDiff 2 f) (hg : ContDiff 2 g) :
  ContDiff 2 (fun x ↦ f x + g x) := trivial

lemma Differentiable.add [Add F] (f g : E → F) (hf : Differentiable f) (hg : Differentiable g) :
  Differentiable (fun x ↦ f x + g x) := trivial

attribute [to_differentiable existing] ContDiff.add
