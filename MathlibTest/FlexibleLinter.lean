import Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Tactic.Linter.UnusedTactic
import Batteries.Linter.UnreachableTactic
import Batteries.Tactic.PermuteGoals

set_option linter.flexible true
set_option linter.unusedVariables false

/-! # Basic tests for the flexible linter

This file contains basic tests for the flexible linter, which do not require any advanced imports.
Anything which requires groups, rings or algebraic structures is considered advanced, and
tests for these can be found in `MathlibTest/ImportHeavyFlexibleLinter.lean`

-/

/--
warning: 'simp at h' is a flexible tactic modifying 'h'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 + 0 = 0) : True := by
  simp at h
  try exact h

-- `subst` does not use the goal
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  subst h
  rfl

-- `by_cases` does not use the goal
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  by_cases a = b
  subst h; rfl
  subst h; rfl

-- `induction` does not use the goal
/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'assumption' uses '⊢'!
---
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'assumption' uses '⊢'!
-/
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  induction a <;> assumption


/--
warning: 'simp at h' is a flexible tactic modifying 'h'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 = 0 ∨ 0 = 0) : True := by
  cases h <;>
    rename_i h <;>
    simp at h
  · exact h
  · assumption --exact h

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'on_goal 2 => · contradiction' uses '⊢'!
---
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  on_goal 2 => · contradiction
  · contradiction

-- `omega` is a follower and `all_goals` is a `combinatorLike`
#guard_msgs in
example {a : Nat} : a + 1 + 0 = 1 + a := by simp; all_goals omega

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'contradiction' uses '⊢'!
---
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  · contradiction
  · contradiction

/--
warning: 'simp at h k' is a flexible tactic modifying 'k'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
warning: 'simp at h k' is a flexible tactic modifying 'h'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} {k : 1 = 1} : True := by
  simp at h k;
  rw [← Classical.not_not (a := True)]
  -- flag the two below vvv do not above ^^^
  rw [← Classical.not_not (a := True)] at k
  rw [← Classical.not_not (a := True)] at h
  assumption

-- `specialize` does not touch, by default, the target
#guard_msgs in
example {a b : Nat} (h : ∀ c, c + a + b = a + c) : (0 + 2 + 1 + a + b) = a + 3 := by
  simp
  specialize h 3
  simp_all

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'exact h.symm' uses '⊢'!
-/
#guard_msgs in
-- `congr` is allowed after `simp`, but "passes along the stain".
example {a b : Nat} (h : a = b) : a + b + 0 = b + a := by
  simp
  congr
  exact h.symm

-- `done` is an allowed follower
#guard_msgs in
example (h : False) : 0 ≠ 0 := by
  try (simp; done)
  exact h.elim

-- `grind` is another flexible tactic.
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  grind

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  · simp_all
  · contradiction

-- forget stained locations, once the corresponding goal is closed
#guard_msgs in
example (n : Nat) : n + 1 = 1 + n := by
  by_cases 0 = 0
  · simp_all
    omega
  · have : 0 ≠ 1 := by
      intro h
      -- should not flag `cases`!
      cases h
    -- should not flag `exact`!
    exact Nat.add_comm ..

/--
warning: 'simp at h' is a flexible tactic modifying 'h'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} {k : 1 = 1} : ¬ ¬ True := by
  simp at h
  rw [← Nat.add_zero 1] at k
  -- flag below vvv do not flag above ^^^
  rw [← Classical.not_not (a := True)] at h
  --exact h -- <-- flagged
  assumption

/--
warning: 'simp at h k' is a flexible tactic modifying 'k'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
warning: 'simp at h k' is a flexible tactic modifying 'h'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} {k : 1 = 1} : True := by
  simp at h k
  rw [← Classical.not_not (a := True)]
  -- flag the two below vvv do not above ^^^
  rw [← Classical.not_not (a := True)] at k
  rw [← Classical.not_not (a := True)] at h
  assumption

/--
warning: 'simp at h' is a flexible tactic modifying 'h'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} : True := by
  simp at h
  rw [← Classical.not_not (a := True)]
  -- flag below vvv do not flag above ^^^
  rw [← Classical.not_not (a := True)] at h
  assumption

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 := by
  simp
  rw [← Classical.not_not (a := False)] at h
  -- flag below vvv do not flag above ^^^
  rwa [← Classical.not_not (a := False)]

/--
warning: 'simp' is a flexible tactic modifying '⊢'…

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: … and 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 ∧ 0 = 1 := by
  constructor
  · simpa
  . simp
    rw [← Classical.not_not (a := False)] at h
    rwa [← Classical.not_not (a := False)]

section test_internals
open Lean Mathlib.Linter Flexible

/-- `flex? tac` logs an info `true` if the tactic is flexible, logs a warning `false` otherwise. -/
elab "flex? " tac:tactic : command => do
  match flexible? tac with
    | true  => logWarningAt tac m!"{flexible? tac}"
    | false => logInfoAt tac m!"{flexible? tac}"

section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
/-- info: false -/#guard_msgs in
flex? done
/-- info: false -/#guard_msgs in
flex? simp only
/-- info: false -/#guard_msgs in
flex? simp_all only
/-- warning: true -/#guard_msgs in
flex? simp
/-- warning: true -/#guard_msgs in
flex? simp_all

end

/-- info: #[h] -/ #guard_msgs in
#eval show CoreM _ from do
  let h := mkIdent `h
  let hc ← `(Lean.Parser.Tactic.elimTarget|$h:ident)
  IO.println s!"{(toStained (← `(tactic| cases $hc))).toArray}"
