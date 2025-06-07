import Mathlib.Tactic.Linter.ForallIntro

set_option linter.forallIntro false

/--
warning: declaration uses 'sorry'
---
warning: replace
  have (_ : Nat) : ∀ {x} z (y : Nat), x + y = z := by
    intros s t u
    refine ?_
    sorry
with
  have (_ : Nat) {x} z (y : Nat) : x + y = z := by
    refine ?_
    sorry
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
warning: replace
  have (_ : Nat) : ∀ {x} z (y : Nat), x + y = z := by
    intros s t u
    refine ?_
    sorry
with
  have (_ : Nat) {x} z (y : Nat) : x + y = z := by
    refine ?_
    sorry
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
warning: replace
  have (_ : Nat) : ∀ x y, ∀ z w, (x + y : Nat) = z + w :=
    by
    intros s t u
    intros s
    refine ?_
    sorry
with
  have (_ : Nat) x y z w : (x + y : Nat) = z + w := by
    refine ?_
    sorry
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have (_ : Nat) : ∀ x y, ∀ z w, (x + y : Nat) = z + w := by
    intros s t u
    intros s
    refine ?_
    sorry
  trivial

/--
warning: declaration uses 'sorry'
---
warning: replace
  have (_ : Nat) : ∀ {x y : Nat}, ∀ z w, x + y = z + w :=
    by
    intros x
    refine ?_
    sorry
with
  have (_ : Nat) {x : Nat} : ∀ {y : Nat}, ∀ z w, x + y = z + w :=
    by
    refine ?_
    sorry
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have (_ : Nat) : ∀ {x y : Nat}, ∀ z w, x + y = z + w := by
    intros x
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
warning: replace
  have : ∀ (n : Nat), n = n := by
    intro s
    rfl
with
  have (n : Nat) : n = n := by rfl
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
info: /home/damiano/Matematica/Lean4/mathlib4/test/ForallIntro.lean:161:20: error: unknown identifier 's'
---
warning: rename 'n' to 's'...
---
warning: ... or rename 's' to 'n'?
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have : ∀ (n : Nat), n = n := by
    intro s
    exact rfl (a := s)
  trivial

/--
warning: declaration uses 'sorry'
---
warning: replace
  have : ∀ (k : Nat), ∀ _, ‹_› = k := by
    intros
    sorry
with
  have (k : Nat) _ : ‹_› = k := by
    intros
    sorry
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have :  ∀ (k : Nat), ∀ _, ‹_› = k := by
    intros
    sorry
  trivial

/--
warning: declaration uses 'sorry'
---
warning: replace
  have : ∀ (a b c d e : Nat) {f g h i : Nat}, a + b + c + d + e = f + g + h + i :=
    by
    intro a b c d e
    sorry
with
  have (a : Nat) (b : Nat) (c : Nat) (d : Nat) (e : Nat) :
    ∀ {f : Nat} {g : Nat} {h : Nat} {i : Nat}, a + b + c + d + e = f + g + h + i := by sorry
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have :  ∀ (a b c d e : Nat) {f g h i : Nat}, a + b + c + d + e = f + g + h + i := by
    intro a b c d e --f --g h i
    sorry
  trivial

/--
warning: replace
  have : ∀ (a b), (a : Nat) = b → a = b := by
    intro a b h
    exact h
with
  have (a) (b) : (a : Nat) = b → a = b := by
    intro h
    exact h
note: this linter can be disabled with `set_option linter.forallIntro false`
-/
#guard_msgs in
set_option linter.forallIntro true in
example : True := by
  have :  ∀ (a b), (a : Nat) = b → a = b := by
    intro a b h
    exact h
  trivial

set_option linter.forallIntro true in
example : True := by
  have :  ∀ {a b c d e}, ∀ {f g h i : Nat}, a + b + c + d + e = f + g + h + i := by
    intro a b c d e f g --h i
    sorry
  trivial
