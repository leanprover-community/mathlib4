import Mathlib.Tactic.Linter.ForallIntro

set_option linter.forallIntro false

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (_ : Nat) {x} z (y : Nat) : x + y = z := by
    refine ?_
    sorry
  trivial
---
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have (_ : Nat) : ∀ {x} z (y : Nat), x + y = z := by
    intros s t u
    refine ?_
    sorry
  trivial

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
theorem hhh : True :=
  by
  have (_ : Nat) {x} z (y : Nat) : x + y = z := by
    refine ?_
    sorry
  trivial
---
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
theorem hhh : True := by
  have (_ : Nat) : ∀ {x} z (y : Nat), x + y = z := by
    intros s t u
    refine ?_
    sorry
  trivial

#guard_msgs in
-- should this trigger the linter and add parentheses around `x : Nat`?
set_option linter.forallIntro true in
example : True := by
  have : ∀ x : Nat, x = x := by
    intro x
    rfl
  trivial

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (_ : Nat) x y z w : (x + y : Nat) = z + w := by
    refine ?_
    sorry
  trivial
---
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have (_ : Nat) : ∀ x y, ∀ z w, (x + y : Nat) = z + w := by
    intros s t
    intros s t
    refine ?_
    sorry
  trivial

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (_ : Nat) {x y : Nat} z w : x + y = z + w := by
    intros
    refine ?_
    sorry
  trivial
---
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have (_ : Nat) : ∀ {x y : Nat}, ∀ z w, x + y = z + w := by
    intros
    refine ?_
    sorry
  trivial

-- the linter does not flag `∀` with no matching `intro(s)`
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have : ∀ x y, (x + y : Nat) = (x + y) := by
    refine ?_
    intros
    rfl
  trivial

/-- `test_rfl` simply "hides" a `∀` quantifier from `linter.forallIntro` -/
abbrev test_rfl : Prop := ∀ x y, (x + y : Nat) = x + y
-- the linter does not flag `intro(s)` with no matching `∀`
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have : test_rfl := by
    intros x y
    rfl
  trivial

/--
warning: Please use
---
example : True := by
  have (n : Nat) : n = n := by rfl
  trivial
---
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have : ∀ (n : Nat), n = n := by
    intro s
    rfl
  trivial

/--
warning: declaration uses 'sorry'
---
warning: Please use
---
example : True :=
  by
  have (k : Nat) _ : ‹_› = k := by
    intros
    sorry
  trivial
---
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have :  ∀ (k : Nat), ∀ _, ‹_› = k := by
    intros
    sorry
  trivial
