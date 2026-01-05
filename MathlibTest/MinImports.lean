import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FunProp.Attr

open Lean.Elab.Command Mathlib.Command.MinImports in
run_cmd liftTermElabM do
  guard ([`A, `A.B.C_3, `A.B.C_2, `A.B.C_1, `A.B.C_0, `A.B.C].map previousInstName
      == [`A, `A.B.C_2, `A.B.C_1, `A.B.C,   `A.B.C,   `A.B.C])

run_cmd
  let stx ← `(variable (a : Nat) in theorem TestingAttributes : a = a := rfl)
  let nm ← Mathlib.Command.MinImports.getDeclName stx
  if `TestingAttributes != nm.eraseMacroScopes then
    Lean.logWarning "Possible misparsing of declaration modifiers!"

/-- info: import Mathlib.Tactic.FunProp.Attr -/
#guard_msgs in
#min_imports in (← `(declModifiers|@[fun_prop]))

-- check that `scoped` attributes do not cause elaboration problems
/-- info: import Lean.Parser.Command -/
#guard_msgs in
#min_imports in
@[scoped simp] theorem XX.YY : 0 = 0 := rfl

namespace X
/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
protected def xxx : Semiring Nat := inferInstance
end X

/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
-- If `#min_imports` were parsing just the syntax, the imports would be `Mathlib/Algebra/Ring/Defs.lean`.
instance : Semiring Nat := inferInstance

/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
instance withName : Semiring Nat := inferInstance

/-- info: import Mathlib.Algebra.Ring.Nat -/
#guard_msgs in
#min_imports in
noncomputable instance : Semiring Nat := inferInstance

/--
info: ℤ : Type
---
info: import Mathlib.Data.Int.Notation
-/
#guard_msgs in
#min_imports in #check ℤ

/-- info: import Mathlib.Data.Int.Notation -/
#guard_msgs in
#min_imports in ℤ

/--
info:
import Batteries.Tactic.Init
import Batteries.Tactic.PermuteGoals
import Mathlib.Tactic.ExtractGoal
-/
#guard_msgs in
#min_imports in (← `(tactic| extract_goal; on_goal 1 => _))

/-- info: import Mathlib.Tactic.NormNum.Basic -/
#guard_msgs in
#min_imports in
lemma uses_norm_num : (0 + 1 : ℕ) = 1 := by norm_num

/-- info: import Mathlib.Tactic.NormNum.Basic -/
#guard_msgs in
#min_imports in uses_norm_num

/--
info: import Mathlib.Tactic.Lemma
import Mathlib.Data.Nat.Notation
---
info: theorem hi.extracted_1_1 (n : ℕ) : n = n := sorry
-/
#guard_msgs in
#min_imports in
lemma hi (n : ℕ) : n = n := by extract_goal; rfl

section Variables

/-- info: import Mathlib.Data.Nat.Notation -/
#guard_msgs in
#min_imports in
def confusableName : (1 : ℕ) = 1 := rfl

variable {R : Type*} [Semiring R]

-- Don't get confused by unused variables.
variable {K : Type*} [Field K]

namespace Namespace

-- The dependency on `Semiring` is only found in the `variable` declaration.
-- We find it by looking up the declaration by name and checking the term,
-- which used to get confused if running in a namespace.

/-- info: import Mathlib.Algebra.Ring.Defs -/
#guard_msgs in
#min_imports in
protected def confusableName : (1 : R) = 1 := rfl

end Namespace

end Variables

section Linter.MinImports

set_option linter.minImports.increases false

set_option linter.minImports false
/-- info: Counting imports from here. -/
#guard_msgs in
#import_bumps

/--
warning: Imports increased to
[Init.Guard, Mathlib.Data.Int.Notation]

New imports: [Init.Guard, Mathlib.Data.Int.Notation]


Note: This linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
#guard (0 : ℤ) = 0

#guard_msgs in
-- no new imports needed here, so no message
#guard (0 : ℤ) = 0

set_option linter.minImports false in
#reset_min_imports

/--
warning: Imports increased to
[Init.Guard, Mathlib.Data.Int.Notation]

New imports: [Init.Guard, Mathlib.Data.Int.Notation]


Note: This linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
-- again, the imports pick-up, after the reset
#guard (0 : ℤ) = 0

/--
warning: Imports increased to
[Mathlib.Tactic.Linter.MinImports]

New imports: [Mathlib.Tactic.Linter.MinImports]


Note: This linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
#reset_min_imports

/--
warning: Imports increased to
[Mathlib.Tactic.NormNum.Basic]

New imports: [Mathlib.Tactic.NormNum.Basic]

Now redundant: [Mathlib.Tactic.Linter.MinImports]


Note: This linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
run_cmd
  let _ ← `(declModifiers|@[fun_prop])
  let _ ← `(tactic|apply @Mathlib.Meta.NormNum.evalNatDvd <;> extract_goal)

end Linter.MinImports

section Linter.UpstreamableDecl

set_option linter.upstreamableDecl true

/--
warning: Consider moving this declaration to the module Mathlib.Data.Nat.Notation.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
theorem propose_to_move_this_theorem : (0 : ℕ) = 0 := rfl

-- By default, the linter does not warn on definitions.
def dont_propose_to_move_this_def : ℕ := 0

set_option linter.upstreamableDecl.defs true in
/--
warning: Consider moving this declaration to the module Mathlib.Data.Nat.Notation.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
def propose_to_move_this_def : ℕ := 0

-- This theorem depends on a local definition, so should not be moved.
#guard_msgs in
theorem theorem_with_local_def : propose_to_move_this_def = 0 := rfl

-- This definition depends on definitions in two different files, so should not be moved.
/--
warning: Consider moving this declaration to the module Mathlib.Tactic.NormNum.Basic.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
theorem theorem_with_multiple_dependencies : True :=
  let _ := Mathlib.Meta.FunProp.funPropAttr
  let _ := Mathlib.Meta.NormNum.evalNatDvd
  trivial

-- Private declarations shouldn't get a warning by default.
private theorem private_theorem : (0 : ℕ) = 0 := rfl

-- But we can enable the option.
set_option linter.upstreamableDecl.private true in
/--
warning: Consider moving this declaration to the module Mathlib.Data.Nat.Notation.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
private theorem propose_to_move_this_private_theorem : (0 : ℕ) = 0 := rfl

-- Private declarations shouldn't get a warning by default, even if definitions get a warning.
set_option linter.upstreamableDecl.defs true in
private def private_def : ℕ := 0

-- But if we enable both options, they should.
set_option linter.upstreamableDecl.defs true in
set_option linter.upstreamableDecl.private true in
/--
warning: Consider moving this declaration to the module Mathlib.Data.Nat.Notation.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
private def propose_to_move_this_private_def : ℕ := 0

/-! Structures and inductives should be treated just like definitions:
no warnings by default, unless we enable the option. -/

structure DontProposeToMoveThisStructure where
  foo : ℕ

inductive DontProposeToMoveThisInductive where
| foo : ℕ → DontProposeToMoveThisInductive
| bar : ℕ → DontProposeToMoveThisInductive → DontProposeToMoveThisInductive

set_option linter.upstreamableDecl.defs true

/--

warning: Consider moving this declaration to the module Mathlib.Data.Nat.Notation.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
structure ProposeToMoveThisStructure where
  foo : ℕ

/--
warning: Consider moving this declaration to the module Mathlib.Data.Nat.Notation.

Note: This linter can be disabled with `set_option linter.upstreamableDecl false`
-/
#guard_msgs in
inductive ProposeToMoveThisInductive where
| foo : ℕ → ProposeToMoveThisInductive
| bar : ℕ → ProposeToMoveThisInductive → ProposeToMoveThisInductive

-- This theorem depends on a local inductive, so should not be moved.
#guard_msgs in
theorem theorem_with_local_inductive : Nonempty ProposeToMoveThisInductive := ⟨.foo 0⟩

end Linter.UpstreamableDecl
