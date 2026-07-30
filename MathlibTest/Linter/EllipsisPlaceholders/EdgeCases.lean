import Mathlib.Tactic.Linter.EllipsisPlaceholders
import Mathlib.Data.List.Basic
import Mathlib.Order.Defs.PartialOrder

set_option linter.style.ellipsisPlaceholders true
set_option linter.unusedVariables false
-- Unit tests use a lower threshold than the default (`4`).
set_option linter.style.ellipsisPlaceholders.minTrailingHoles 2

def edgeFn (a b c : Nat) : Nat := a + b + c
def edgeFnOpt (a : Nat) (b : Nat := 0) (c : Nat := 0) : Nat := a + b + c
def edgeFnFour (a b c d : Nat) : Nat := a + b + c + d
def pipeWrap (a b : Nat) : Nat := a + b

section ExplicitApps

variable {α : Type u} {β : Type v}

def instFn [Inhabited α] [Inhabited β] (x : α) (y : β) : Nat := 0

-- `@`-explicit applications are never rewritten (`..` does not preserve binder slots).
#guard_msgs(drop warning, drop info) in
#check @instFn _ _ _ _

end ExplicitApps

section TypedHoles

-- Typed trailing holes must not become `..` (type annotations guide elaboration).
#guard_msgs(drop warning, drop info) in
#check edgeFn 1 (_ : Nat) (_ : Nat)

#guard_msgs(drop warning, drop info) in
#check edgeFnFour 1 (_ : Nat) 3 _

-- Any typed hole in the trailing suffix disqualifies the whole application.
#guard_msgs(drop warning, drop info) in
#check edgeFn 1 _ (_ : Nat)

end TypedHoles

section PipeProjection

-- Lints the inner `app` node (`pipeWrap _ _`), not the surrounding `id (...)`.
/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check id (pipeWrap _ _)

end PipeProjection

section OptParam

#guard_msgs(drop warning, drop info) in
#check edgeFnOpt 1 _ _

end OptParam

section LetBindings

-- The expression in a let-binding should be linted (was incorrectly skipped before).
/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check (let x := edgeFn 1 _ _; x)

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
#check (fun n : Lean.Name => if let .str _ _ := n then edgeFn 1 _ _ else 0)

end Patterns

section LocalAndParenthesized

variable (localFn : Nat → Nat → Nat)

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check localFn _ _

/--
warning: Replace 2 trailing `_` placeholders with `..`.

Note: This linter can be disabled with `set_option linter.style.ellipsisPlaceholders false`
-/
#guard_msgs(warning, drop info) in
#check edgeFn 1 (_) (_)

end LocalAndParenthesized

section ExplicitUniv

universe u

def univFn {α : Type u} (x : α) (y : α) : α := x

#guard_msgs(drop warning, drop info) in
#check @univFn.{u} _ _ _

end ExplicitUniv

section SyntheticHoles

def sixArg (a b c d e f : Nat) : Nat := a

def mixedTail (a b c d e f : Nat) : Nat := a

-- `?_` in the hole suffix stops linting even when plain `_` follow
#guard_msgs(drop warning, drop info) in
#check sixArg 1 _ _ _ ?_ ?_

#guard_msgs(drop warning, drop info) in
#check mixedTail _ _ _ ?_ _ _

-- six plain trailing `_` still lint
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
#check edgeFnFour _ _ _ _

end ProofBodySkip

section PartialApplication

variable {α : Type*} [Preorder α] {a b c : α}

-- Trailing `_` on a partial application must not become `..` (would fully apply implicits).
#guard_msgs(drop warning, drop info) in
#check Preorder.le_trans _ _ _

#guard_ellipsis_rewrites
example : (a ≤ b → b ≤ c → a ≤ c) := Preorder.le_trans _ _ _

-- Proof-body `exact` with trailing holes (ModifyLast): must not rewrite to `..`.
example (hd hd' : α) (tl' : List α) : hd' :: tl' ≠ [] := by
  all_goals exact List.cons_ne_nil _ _

end PartialApplication
