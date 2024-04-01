import Std.Tactic.PermuteGoals
import Mathlib.Tactic.FlexibleLinter

set_option warningAsError true

-- for some reason, disabling and re-enabling the linter means that
-- `#guard_msgs` actually catches the output!
set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 + 0 = 0) : True := by
  simp at h
  try exact h

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 = 0 ∨ 0 = 0) : True := by
  cases h <;>
    rename_i h <;>
    simp at h
  · exact h
  · assumption --exact h

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
---
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  on_goal 2 => · contradiction
  · contradiction

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
---
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  · contradiction
  · contradiction

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h k' stains 'k'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
error: 'simp at h k' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'contradiction' uses '⊢'!
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

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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


set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h k' stains 'k'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
error: 'simp at h k' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp at h' stains 'h'... [linter.flexible]
---
info: ... and 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
-/
#guard_msgs in
-- `simp at h` stains `h` but not other locations
example {h : 0 = 0} : True := by
  simp at h
  rw [← Classical.not_not (a := True)]
  -- flag below vvv do not flag above ^^^
  rw [← Classical.not_not (a := True)] at h
  assumption

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 := by
  simp
  rw [← Classical.not_not (a := False)] at h
  -- flag below vvv do not flag above ^^^
  rwa [← Classical.not_not (a := False)]

set_option linter.flexible false in
set_option linter.flexible true in
/--
error: 'simp' stains '⊢'... [linter.flexible]
---
info: ... and 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 ∧ 0 = 1 := by
  constructor
  · simpa
  . simp
    rw [← Classical.not_not (a := False)] at h
    rwa [← Classical.not_not (a := False)]

section test_internals
open Lean Mathlib.Linter.flexible

/-- `flex? tac` logs an info `true` if the tactic is flexible, logs a warning `false` otherwise. -/
elab "flex? " tac:tactic : command => do
  match flexible? tac with
    | true  => logWarningAt tac m!"{flexible? tac}"
    | false => logInfoAt tac m!"{flexible? tac}"

/-- info: false -/#guard_msgs in
flex? done
/-- info: false -/#guard_msgs in
flex? simp only
/-- info: false -/#guard_msgs in
flex? simp_all only
/-- error: true -/#guard_msgs in
flex? simp
/-- error: true -/#guard_msgs in
flex? simp_all

/-- info: #[h] -/ #guard_msgs in
#eval show CoreM _ from do
  let h := mkIdent `h
  let hc : TSyntax `Lean.Parser.Tactic.casesTarget := ⟨h⟩
  IO.println s!"{toStained (← `(tactic| cases $hc))}"
