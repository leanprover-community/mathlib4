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

-- Artificially simplified definition, hence the unused arguments.
def Foo (_n _m : ℕ) (f : E → F) : Prop := ∀ x, f x = f x

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
/-- info: Test.Foo3.{u_1, u_2} {E : Type u_1} {F : Type u_2} (_m : ℕ) (f : E → F) : Prop -/
#guard_msgs in
#check Foo3

set_option linter.translate.overwrite false

-- Removing multiple arguments is fine
attribute [to_differentiable existing (omit := 3 4) Bar] Foo

-- Specifying an attribute multiple times again is just fine, nothing happens.
attribute [to_differentiable existing (omit := 3 4 4 3 3 4) Bar] Foo

-- The to_additive machinery checks that the new declaration really has the same type:
-- if there is a mismatch, there is a warning.
/--
error: `to_differentiable` validation failed: expected
  {E : Type _} → {F : Type _} → ℕ → (E → F) → Prop
but `Bar` has type
  {E : Type u_1} → {F : Type u_2} → (E → F) → Prop
-/
#guard_msgs in
attribute [to_differentiable existing (omit := 3) Bar] Foo

-- Omission arguments are treated as if they were in sorted order.
attribute [to_differentiable existing (omit := 4 3) Bar] Foo

-- Omitting arguments together with the dual option errors. TODO can we test this? Is fine here.

-- Specifying overlapping arguments to omit and reorder errors.
-- On first sight, this is contradictory. On second sight, this could be carefully specified,
-- but there is no use case yet. If this changes, this may be revisited.
/--
error: argument(s) [3, 4] are supposed to be both omitted and reordered: this is currently not supported.
-/
#guard_msgs in
attribute [to_differentiable (reorder := 3 4) (omit := 3 4)] Foo

/--
error: argument(s) [2] are supposed to be both omitted and reordered: this is currently not supported.
-/
#guard_msgs in
attribute [to_differentiable (reorder := 2 4) (omit := 2 3)] Foo

end inputValidation

-- Artificially simplified definitions (which hence contain unused variables).
def ContDiff (R : Type*) [Group R] {E F : Type*} [Group E] [Group F] (_n : ℕ) (f : E → F) : Prop :=
  ∀ x, f x = f x

def Differentiable (R : Type*) [Group R] {E F : Type*} [Group E] [Group F] (f : E → F) : Prop :=
  ∀ x, f x = f x

attribute [to_differentiable existing (omit := 7) Differentiable] ContDiff

variable {R : Type*} [Group R] {E F : Type*} [Group E] [Group F]

-- Lemmas about a concrete function.
def sin : R → R := @id R

lemma contDiff_sin : ContDiff R 2 (sin : R → R) := fun _ ↦ rfl

lemma differentiable_sin : Differentiable R (sin : R → R) := fun _ ↦ rfl

attribute [to_differentiable existing differentiable_sin] contDiff_sin

variable {n : Nat}

@[to_differentiable differentiable_sin']
lemma contDiff_sin' : ContDiff R n (sin : R → R) := fun _ ↦ rfl

@[to_differentiable differentiable_sin'']
lemma contDiff_sin'' : ContDiff R 0 (sin : R → R) := fun _ ↦ rfl

@[to_differentiable differentiable_sin''']
lemma contDiff_sin''' : ContDiff R 0 (sin : R → R) := fun _ ↦ rfl

@[to_differentiable]
lemma ContDiff.add [Add F] {f g : E → F} (_hf : ContDiff R 2 f) (_hg : ContDiff R 2 g) :
  ContDiff R 2 (fun x ↦ f x + g x) := fun _ ↦ rfl

-- TODO: need to manually ask to omit the implicit argument `n`
@[to_differentiable (omit := 7)]
lemma ContDiff.add' [Add F] {f g : E → F} (_hf : ContDiff R n f) (_hg : ContDiff R n g) :
  ContDiff R n (fun x ↦ f x + g x) := fun _ ↦ rfl

@[to_differentiable (omit := 3) differentiable_one]
lemma contDiff_one [One R] : ContDiff R n (fun (_ : R) ↦ (1 : R)) := fun _ ↦ rfl

@[to_differentiable (omit := 3) differentiable_zero]
lemma contDiff_zero [Zero R] : ContDiff R n (fun (_ : R) ↦ (0 : R)) := fun _ ↦ rfl

-- Translating a proof involving other lemmas.
@[to_differentiable bar]
lemma foo [Add R] {f : R → R} (hf : ContDiff R n f) : ContDiff R n (fun x ↦ f x + sin x) :=
  hf.add contDiff_sin

-- Matching lemmas with a different proof.
lemma ContDiff.differentiable {f : R → R} (_hf : ContDiff R n f) (_hn : n ≠ 0) :
    Differentiable R f :=
  fun _ ↦ rfl

def cos : R → R := @id R

lemma contDiff_cos : ContDiff R n (cos : R → R) := fun _ ↦ rfl

lemma differentiable_cos : Differentiable R (cos : R → R) :=
  contDiff_cos.differentiable (n := 1) (by simp)

-- TODO: need to manually specify the `n` argument to be removed!
attribute [to_differentiable existing (omit := 3) differentiable_cos] contDiff_cos

-- TODO: need to manually specify the `n` argument to be removed!
@[to_differentiable (omit := 3) bar']
lemma foo' [Add R] {f : R → R} (hf : ContDiff R n f) : ContDiff R n (fun x ↦ f x + cos x) :=
  hf.add contDiff_cos

-- TODO: why does this not fail when I comment `differentiable_cos`?
/--
info: Test.bar'.{u_1} {R : Type u_1} [Group R] [Add R] {f : R → R} (hf : Differentiable R f) :
  Differentiable R fun x => f x + cos x
-/
#guard_msgs in
#check bar'

-- Translating a theorem with a hypothesis on `n`.
-- TODO: currently, we translate both `n` and the hypothesis
def aux : R → R := @id R

@[to_differentiable differentiable_aux]
lemma contDiff_aux (_hn : n ≠ 0) : ContDiff R n (aux : R → R) := fun _ ↦ rfl

/--
info: Test.differentiable_aux.{u_1} {R : Type u_1} [Group R] {n : ℕ} (_hn : n ≠ 0) : Differentiable R aux
-/
#guard_msgs in
#check differentiable_aux

-- TODO: add test for a typeclass argument involving n, and translating that to 1
-- and implement that feature, most importantly!

end Test
