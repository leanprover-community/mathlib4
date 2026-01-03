module

public import Mathlib.Tactic.Linter.FlexibleLinter
import all Mathlib.Tactic.Linter.FlexibleLinter
import Mathlib.Tactic.Linter.UnusedTactic
import Batteries.Linter.UnreachableTactic
import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.TacticAnalysis.Declarations -- only needed temporarily for the `lia` shim

set_option linter.flexible true
set_option linter.unusedVariables false

/-! # Basic tests for the flexible linter

This file contains basic tests for the flexible linter, which do not require any advanced imports.
Anything which requires groups, rings or algebraic structures is considered advanced, and
tests for these can be found in `MathlibTest/ImportHeavyFlexibleLinter.lean`

-/

/--
warning: 'simp at h' is a flexible tactic modifying 'h'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 + 0 = 0) : True := by
  simp at h
  try exact h

/--
warning: 'simp_all' is a flexible tactic modifying '⊢'. Try 'simp_all?' and use the suggested 'simp_all only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp_all only [Nat.add_zero]
---
info: 'exact Nat.le_succ_of_le h' uses '⊢'!
-/
#guard_msgs in
example {a b : Nat} (h : a ≤ b) : a + 0 ≤ b + 1 := by
  simp_all
  exact Nat.le_succ_of_le h

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
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: 'assumption' uses '⊢'!
---
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: 'assumption' uses '⊢'!
-/
#guard_msgs in
example {a b : Nat} (h : a = b) : a + 0 = b := by
  simp
  induction a <;> assumption


/--
warning: 'simp at h' is a flexible tactic modifying 'h'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'exact h' uses 'h'!
-/
#guard_msgs in
example (h : 0 = 0 ∨ 0 = 0) : True := by
  cases h <;>
    rename_i h <;>
    simp at h
  · exact h
  · assumption --exact h

/--
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one, and_self]
---
info: 'on_goal 2 => · contradiction' uses '⊢'!
---
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one, and_self]
---
info: 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  on_goal 2 => · contradiction
  · contradiction

-- `lia` is a follower and `all_goals` is a `combinatorLike`
#guard_msgs in
example {a : Nat} : a + 1 + 0 = 1 + a := by simp; all_goals lia

/--
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one, and_self]
---
info: 'contradiction' uses '⊢'!
---
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one, and_self]
---
info: 'contradiction' uses '⊢'!
-/
#guard_msgs in
example (h : 0 = 1 ∨ 0 = 1) : 0 = 1 ∧ 0 = 1 := by
  cases h <;> simp
  · contradiction
  · contradiction

/--
warning: 'simp at h k' is a flexible tactic modifying 'k'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
warning: 'simp at h k' is a flexible tactic modifying 'h'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.add_zero]
---
info: 'exact h.symm' uses '⊢'!
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

-- `ac_rfl` is an allowed follower
#guard_msgs in
example {a b c d : Nat} (h : False) (h' : d = a) : a + (b + c) = (b + d) + c := by
  simp [h']
  ac_rfl

-- `grind` is another flexible tactic,
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  grind

-- as are its `grobner` and `lia` front-ends.
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  grobner

-- `lia` is another flexible tactic.
#guard_msgs in
example {x y : Nat} : 0 + x + (y + x) = x + x + y := by
  simp
  lia

/--
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one, and_self]
---
info: 'contradiction' uses '⊢'!
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
    lia
  · have : 0 ≠ 1 := by
      intro h
      -- should not flag `cases`!
      cases h
    -- should not flag `exact`!
    exact Nat.add_comm ..

/--
warning: 'simp at h' is a flexible tactic modifying 'h'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [not_true_eq_false, not_false_eq_true] at h
---
info: 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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
warning: 'simp at h k' is a flexible tactic modifying 'k'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'rw [← Classical.not_not (a := True)] at k' uses 'k'!
---
warning: 'simp at h k' is a flexible tactic modifying 'h'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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
warning: 'simp at h' is a flexible tactic modifying 'h'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: 'rw [← Classical.not_not (a := True)] at h' uses 'h'!
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
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one]
---
info: 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
-/
#guard_msgs in
example {h : False} : 0 = 1 := by
  simp
  rw [← Classical.not_not (a := False)] at h
  -- flag below vvv do not flag above ^^^
  rwa [← Classical.not_not (a := False)]

/--
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [Nat.zero_ne_one]
---
info: 'rwa [← Classical.not_not (a := False)]' uses '⊢'!
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


open Lean Elab Command in
elab "ff " cmd:command : command => do
  elabCommand cmd
  dbg_trace quickCheck cmd
  let bys := cmd.raw.filter (·.isOfKind ``Parser.Tactic.tacticSeq1Indented)
  --dbg_trace bys.map (·[0].getArgs) |>.map (·.size)
  --for s in bys.flatMap (·[0].getArgs) do
  --  logInfo <| m!"{InspectSyntax.toMessageData s} -- '{s.getAtomVal}'"
  let tacticSequences := bys.map (·[0].getArgs.filter fun t => ((!t.isOfKind `null) && (t.getAtomVal != ";")))
  for s in tacticSequences do
    logInfo m!"syntaxArrayFlexNoNeed: {syntaxArrayFlexNoNeed s}" ---- '{s}'"
  let withoutLastTactic := tacticSequences --.map (·.pop)
  logInfo <| m!"\n\n".joinSep (withoutLastTactic.map (m!"{·}")).toList
  for by1 in bys do
    match by1 with
    | `(tacticSeq| ($ts:tacticSeq)) =>
      dbg_trace "found"
      --continue
    | _ => continue

/--
info: syntaxArrayFlexNoNeed: true
---
info: [trivial]
-/
#guard_msgs in
ff
example : True := by
  trivial;

/--
info: syntaxArrayFlexNoNeed: false
---
info: [simp <;> trivial]
---
warning: 'trivial' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
---
warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
-/
#guard_msgs in
ff
example : True := by
  simp <;> trivial;

/--
info: syntaxArrayFlexNoNeed: false
---
info: [simp <;> refine ?_, simp [h]]
---
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [and_true]
---
info: 'refine ?_' uses '⊢'!
-/
#guard_msgs in
ff
example (h : False) : False ∧ True := by
  simp <;> refine ?_
  simp [h]

/--
info: syntaxArrayFlexNoNeed: false
---
info: [simp, simp [h]]
-/
#guard_msgs in
ff
example (h : False) : False ∧ True := by
  simp
  simp [h]

/--
info: syntaxArrayFlexNoNeed: true
---
info: [simp only [and_true], simp [h]]
-/
#guard_msgs in
ff
example (h : False) : False ∧ True := by
  simp only [and_true]
  simp [h]


/--
error: `simp` made no progress
---
info: syntaxArrayFlexNoNeed: true
---
info: [simp only <;> refine ?_, simp [h]]
-/
#guard_msgs in
ff
example (h : False) : False ∧ True := by
  simp only <;> refine ?_
  simp [h]

/--
info: syntaxArrayFlexNoNeed: false
---
info: [simp <;> refine ?_, simp [h]]
---
warning: 'simp' is a flexible tactic modifying '⊢'. Try 'simp?' and use the suggested 'simp only [...]'. Alternatively, use `suffices` to explicitly state the simplified form.

Note: This linter can be disabled with `set_option linter.flexible false`
---
info: Try this:
  [apply] simp only [and_true]
---
info: 'refine ?_' uses '⊢'!
-/
#guard_msgs in
ff
example (h : False) : False ∧ True := by
  simp <;> refine ?_
  simp [h]


/--
info: syntaxArrayFlexNoNeed: true
---
info: syntaxArrayFlexNoNeed: false
---
info: syntaxArrayFlexNoNeed: true
---
info: syntaxArrayFlexNoNeed: false
---
info: syntaxArrayFlexNoNeed: false
---
info: syntaxArrayFlexNoNeed: false
---
info: [refine ?_, simp]

[exact by refine ?_; simp]

[simpa]

[simp [(by simpa : False)] <;> rw []]

[apply id, refine by simp [(by simpa : False)] <;> rw []]

[constructor,
 · exact by refine ?_; simp,
 · apply id
   refine by simp [(by simpa : False)] <;> rw []]
---
warning: 'rw []' tactic does nothing

Note: This linter can be disabled with `set_option linter.unusedTactic false`
---
warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
-/
#guard_msgs in
ff
example (h : False) : True ∧ False := by
  constructor
  · exact by refine ?_; simp
  · apply id
    refine by simp [(by simpa : False)] <;> rw []
