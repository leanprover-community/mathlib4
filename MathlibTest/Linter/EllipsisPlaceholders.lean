import Mathlib.Tactic.Linter.EllipsisPlaceholders
import Mathlib.Data.List.Basic
import Mathlib.Order.Defs.PartialOrder

set_option linter.style.ellipsisPlaceholders true
set_option linter.unusedVariables false

/-! Tests for the `ellipsisPlaceholders` linter.

The default `linter.style.ellipsisPlaceholders.minTrailingHoles` is `4` (lint at `≥ 4`
trailing `_`). Tests that need a lower threshold set it explicitly with `set_option … in`.
-/

def ellipsisTestFn (a b c : Nat) : Nat := a + b + c
def ellipsisTestFnFour (a b c d : Nat) : Nat := a + b + c + d
def ellipsisTestFnOpt (a : Nat) (b : Nat := 0) (c : Nat := 0) : Nat := a + b + c
def ellipsisTestFnAuto (a : Nat) (b : Nat := by decide) : Nat := a + b
def pipeWrap (a b : Nat) : Nat := a + b
def sixArg (a b c d e f : Nat) : Nat := a
def mixedTail (a b c d e f : Nat) : Nat := a
def batchFn (a b c d : Nat) : Nat := a

def mathlibStyleThree {α β γ : Type u} (_x : α) (_y : β) (_z : γ) : Nat := 0
def mathlibStyleWithMid {α β γ : Type u} (x : α) (y : β) (_z : γ) : α := x
def fourArg (a : Nat) (b : Nat) (c : Nat) (d : Nat) : Nat := a + b + c + d

section DefaultThreshold

-- Default `minTrailingHoles` is `4` (no override).

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnFour 1 _ _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnFour 1 _ _ _

#guard_msgs(drop warning, drop info) in
#check ellipsisTestFnFour 1 2 3 _

/--
warning: Replace 4 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check ellipsisTestFnFour _ _ _ _

-- Should NOT lint: `?_` anywhere in the hole suffix
#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _ ?_ ?_

#guard_msgs(drop warning, drop info) in
#check mixedTail _ _ _ ?_ _ _

section Min2

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 _ _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 _

end Min2

section Min3

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 3 in
#check ellipsisTestFn 1 _ _

/--
warning: Replace 3 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 3 in
#check ellipsisTestFnFour 1 _ _ _

end Min3

end DefaultThreshold

section Basic

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 _ _

/--
warning: Replace 3 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnFour 1 _ _ _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnFour 1 2 3 _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnFour 1 ..

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnFour 1 _ 3 _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnOpt 1 _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnOpt 1 _ _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnAuto 1 _

set_option linter.style.ellipsisPlaceholders false in
#guard_msgs(drop warning, drop info) in
#check ellipsisTestFn 1 _ _

example : Nat := by
  set_option linter.style.ellipsisPlaceholders true in
  exact ellipsisTestFn 1 2 3

-- Typed holes are never rewritten.
#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 (_ : Nat) (_ : Nat)

end Basic

section EdgeCases

section ExplicitApps

variable {α : Type u} {β : Type v}

def instFn [Inhabited α] [Inhabited β] (x : α) (y : β) : Nat := 0

-- `@`-explicit applications are never rewritten (`..` does not preserve binder slots).
#guard_msgs(drop warning, drop info) in
#check @instFn _ _ _ _

end ExplicitApps

section TypedHoles

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 (_ : Nat) (_ : Nat)

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFnFour 1 (_ : Nat) 3 _

-- Any typed hole in the trailing suffix disqualifies the whole application.
#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 _ (_ : Nat)

end TypedHoles

section PipeProjection

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check id (pipeWrap _ _)

end PipeProjection

section LetBindings

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check (let x := ellipsisTestFn 1 _ _; x)

-- The tuple pattern in a let-pat binding must not be flagged (it's not an application).
#guard_msgs(drop warning, drop info) in
#check (let (a, b) := (1, 2); a + b)

end LetBindings

section Patterns

-- Patterns themselves must not lint; empty expected messages (after dropping `#check` info)
-- fails if a warning appears.
#guard_msgs(drop info) in
#check (fun n : Lean.Name => match n with | .str _ _ => true | _ => false)

#guard_msgs(drop info) in
#check (fun n : Lean.Name => if let mod@(.str _ _) := n then mod else n)

-- Term positions of `if let` (scrutinee / then / else) still lint when reachable.
#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check (fun n : Lean.Name => if let .str _ _ := n then ellipsisTestFn 1 _ _ else 0)

end Patterns

section LocalAndParenthesized

variable (localFn : Nat → Nat → Nat)

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check localFn _ _

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check ellipsisTestFn 1 (_) (_)

end LocalAndParenthesized

section ExplicitUniv

universe u

def univFn {α : Type u} (x : α) (y : α) : α := x

#guard_msgs(drop warning, drop info) in
#check @univFn.{u} _ _ _

end ExplicitUniv

section SyntheticHoles

-- `?_` in the hole suffix stops linting even when plain `_` follow
#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _ ?_ ?_

#guard_msgs(drop warning, drop info) in
#check mixedTail _ _ _ ?_ _ _

-- six plain trailing `_` still lint at the default threshold
/--
warning: Replace 6 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check sixArg _ _ _ _ _ _

end SyntheticHoles

section ProofBodySkip

-- Declaration bodies with live `_` holes are skipped (see NoetherNormalization regression).
-- Top-level `#check` with the same shape is still linted.
/--
warning: Replace 4 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check ellipsisTestFnFour _ _ _ _

end ProofBodySkip

section PartialApplication

variable {α : Type*} [Preorder α] {a b c : α}

-- Trailing `_` on a partial application must not become `..` (would fully apply implicits).
#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check Preorder.le_trans _ _ _

set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#guard_ellipsis_rewrites
example : (a ≤ b → b ≤ c → a ≤ c) := Preorder.le_trans _ _ _

-- Proof-body `exact` with trailing holes (ModifyLast): must not rewrite to `..`.
example (hd hd' : α) (tl' : List α) : hd' :: tl' ≠ [] := by
  all_goals exact List.cons_ne_nil _ _

end PartialApplication

end EdgeCases

section Dogfood

/--
warning: Replace 3 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check mathlibStyleThree _ _ _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check mathlibStyleWithMid _ 0 _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check mathlibStyleThree 0 _ 0

-- Named arg before trailing holes (common in mathlib)
/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#check fourArg 1 (b := 2) _ _

end Dogfood

section BatchValidation

-- Batch validation: apply every linter rewrite in this command and re-elaborate.
#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#guard_ellipsis_rewrites
#check batchFn 1 _ _

def instBatch {α : Type u} {β : Type v} [Add α] [Add β] (f : α → β) : Nat := 0

-- `@`-explicit: no rewrites collected.
#guard_ellipsis_rewrites
#check @instBatch _ _ _ _

#guard_msgs(drop warning, drop info) in
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2 in
#guard_ellipsis_rewrites
#check sixArg _ _ _ _ _ _

end BatchValidation
