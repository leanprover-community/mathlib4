module
public meta import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.Linter.DroppableHypotheses

set_option linter.all false

namespace DroppableHypothesesTest

-- Disabled by default.
#guard_msgs in
theorem disabled (h : True) : True := by trivial

-- Enabling every ordinary linter must not enable expensive replay trials.
#guard_msgs (drop info) in
set_option linter.all true in
theorem allLinters (P : Prop) (_h _k : P) : P := by assumption

set_option linter.droppableHypotheses true

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem unused (h : True) : True := by trivial

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem defaultArgument (h : True := by trivial) : True := by trivial

-- Failed trials must not leak their unknown-identifier or unsolved-goal errors.
#guard_msgs in
theorem necessary (P : Prop) (h : P) : P := h

-- Each name in a grouped binder is tried separately. The original proof uses one of them.
-- Both can be dropped individually, but not together.
/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Parameter `k` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem automation (P : Prop) (h k : P) : P := by assumption

-- Every replay must restore the original declaration, including its arguments.
example : (P : Prop) → P → P → P := automation

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Parameter `k` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem implicit {h : True} ⦃k : True⦄ : True := by trivial

/--
warning: Parameter `[Nonempty α]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Parameter `[Inhabited α]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem instances (α : Type) [Nonempty α] [Inhabited α] : Nonempty α := by infer_instance

section
variable {α : Type} [Nonempty α] [Inhabited α]

/--
warning: Section parameter `[Nonempty α]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Section parameter `[Inhabited α]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem sectionInstances : Nonempty α := by infer_instance

-- An omitted variable is already absent, so deleting it is not a finding.
#guard_msgs in
omit [Inhabited α] in
theorem omitted : Nonempty α := by infer_instance
end

section
variable (h k : True)
include h k

/--
warning: Section parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Section parameter `k` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem included : True := by trivial

example : True → True → True := included
end

section
variable (unusedSectionVariable : Nat)

#guard_msgs in
theorem unusedSection : True := by trivial
end

-- `autoImplicit` must not silently reintroduce a deleted binder.
#guard_msgs in
set_option autoImplicit true in
theorem autoImplicitGuard (P : Prop) (h : P) : P := h

-- Name capture must not turn a general statement into a special case about a global constant.
def n : Nat := 0

#guard_msgs in
theorem capture (n : Nat) : n = n := by rfl

-- Dropping a data-carrying instance must not switch the meaning of the conclusion.
class Selected where
  value : Nat

/--
warning: Parameter `[a : Selected]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem selectedInstance [a : Selected] [b : Selected] : Selected.value = Selected.value := by rfl

-- Anonymous instances align by type; each can be removed independently.
/--
warning: Parameter `[Selected]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Parameter `[Selected]` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem ambiguousInstances [Selected] [Selected] : Selected.value = Selected.value := by rfl

-- Repeated binder names also permit independent removals when reinsertion recovers the type.
/--
warning: Parameter `x` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
---
warning: Parameter `x` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem ambiguousNames (x : Nat) (x : Nat) : x = x := by rfl

-- The original theorem must not be available during replay.
#guard_msgs in
theorem selfReference (h : True) : True := by
  first | exact h | exact selfReference True.intro

-- A replay that inserts `sorry` without errors is not a successful trial.
#guard_msgs in
theorem sorryReplay (h : True) : True := by
  first | exact h | sorry

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem originalSorry (h : True) : True := by sorry

-- A failed proof may leave auxiliary declarations behind; none should escape the trial.
#guard_msgs in
theorem auxiliary (h : False) : False := by
  have helper : False := h
  exact helper

open Lean Elab Tactic in
elab "spend_trial_heartbeats" : tactic => do
  for _ in [:10000] do
    discard <| Meta.mkFreshExprMVar (mkConst ``True)

-- A timed-out trial is silent and leaves the original declaration intact.
#guard_msgs in
set_option linter.droppableHypotheses.maxHeartbeats 1 in
theorem timeout (h : True) : True := by
  first | exact h | spend_trial_heartbeats; exact True.intro

example : True → True := timeout

-- The same trial succeeds with the default budget.
/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem adequateBudget (h : True) : True := by
  first | exact h | spend_trial_heartbeats; exact True.intro

open Lean Elab Tactic in
elab "warn_in_trial" : tactic => logWarning "trial warning"

-- A warning in the alternative proof must not make a successful replay fail.
/--
error: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
set_option warningAsError true in
theorem warningIsNotFailure (h : True) : True := by
  first | exact h | warn_in_trial; exact True.intro

-- Declarations with private or qualified names are supported.
/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
private theorem hidden (h : True) : True := by trivial

-- Original declarations retain normal module visibility when using private field notation.
public structure PrivateFieldTest where
  value : Nat

#guard_msgs in
private theorem PrivateFieldTest.helper (x : PrivateFieldTest) (h : x.value = 0) :
    x.value = 0 := h

#guard_msgs in
public theorem PrivateFieldTest.useHelper (x : PrivateFieldTest) (h : x.value = 0) :
    x.value = 0 := x.helper h

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem Qualified.name (h : True) : True := by trivial

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
protected theorem Qualified.protectedName (h : True) : True := by trivial

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
theorem _root_.droppableRootName (h : True) : True := by trivial

namespace Opened
theorem ambiguousRootName (h : True) : True := h
end Opened

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
open Opened in
theorem ambiguousRootName (h : True) : True := by trivial

-- Per-command disabling works.
#guard_msgs in
set_option linter.droppableHypotheses false in
theorem locallyDisabled (h : True) : True := by trivial

end DroppableHypothesesTest

-- Per-command enabling works even when disabled in the surrounding scope.
set_option linter.droppableHypotheses false

/--
warning: Parameter `h` can be dropped: the declaration and its existing proof re-elaborate without it.

Note: This linter can be disabled with `set_option linter.droppableHypotheses false`
-/
#guard_msgs in
set_option linter.droppableHypotheses true in
theorem droppableLocallyEnabled (h : True) : True := by trivial
