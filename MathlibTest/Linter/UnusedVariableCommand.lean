/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.UnusedVariableCommand

/-! # Tests for the `unusedVariableCommand` linter

The linter reports `variable` binders that no declaration in their scope uses. It fires when
the scope closes: at its `end` command, or at a terminal command (`#exit`, end of file).
-/

set_option linter.unusedVariableCommand true

-- An unused binder: the linter fires at the `end` of the section.
section
variable (unusedNat : Nat)

/--
warning: variable 'unusedNat' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- A binder that a theorem uses: no warning.
section
variable (usedNat : Nat)

theorem usedNat_eq : usedNat = usedNat := rfl

#guard_msgs in
end

-- A binder that only an `example` uses: no warning. `example` adds no declaration to the
-- environment, so the identifier occurrences in the command syntax provide the usage.
section
variable (exampleNat : Nat)

example : exampleNat = exampleNat := rfl

#guard_msgs in
end

-- A binder that a declaration includes only as a dependency: no warning. The syntax of
-- `depFin_eq` does not mention `depN`, but the leading telescope of `depFin_eq` binds it.
section
variable (depN : Nat) (depFin : Fin depN)

theorem depFin_eq : depFin = depFin := rfl

#guard_msgs in
end

-- Two binders, one used: the linter reports only the unused one.
section
variable {usedT unusedT : Type}

def idUsed (t : usedT) : usedT := t

/--
warning: variable 'unusedT' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- Nested scopes: a declaration in the inner namespace uses the outer binder; the unused
-- inner binder gets its warning at `end Inner`.
section
variable (outerN : Nat)

namespace Inner
variable (innerUnused : Bool)

def useOuter : Nat := outerN

/--
warning: variable 'innerUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end Inner

#guard_msgs in
end

-- A `variable (annA)` annotation update rebuilds the binder group: the linter still tracks
-- each binder once and reports each unused binder once.
section
variable {annA annB : Nat}
variable (annA)

/--
warning: variable 'annA' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
---
warning: variable 'annB' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- `include` is binder management, not usage: the binder stays unused.
section
variable (hTrue : True)
include hTrue

/--
warning: variable 'hTrue' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- `omit` is binder management too: the binder stays unused.
section
variable (hOmit : True)
omit hOmit

/--
warning: variable 'hOmit' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- A strict-implicit binder is tracked like the other named binder kinds.
section
variable ⦃strictUnused : Nat⦄

/--
warning: variable 'strictUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- An instance binder that a declaration uses only through synthesis: no warning. No identifier
-- of the command names `instDec`, and the leading telescope of `decideSynthP` binds it.
section
variable {synthP : Prop} [instDec : Decidable synthP]

def decideSynthP : Bool := decide synthP

#guard_msgs in
end

-- An anonymous instance binder carries no ident, so the linter never reports it. Only the named
-- binder of the scope gets a report, although the removal of `anonT` also needs the removal of
-- the instance binder that mentions it.
section
variable {anonT : Type} [Nonempty anonT]

/--
warning: variable 'anonT' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- A binder that only the type of another binder mentions stays unused: a `variable` command is
-- not a use. The report names both binders, which need removal together.
section
variable (chainA : Nat) (chainB : Fin chainA)

/--
warning: variable 'chainA' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
---
warning: variable 'chainB' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- An inner scope does not re-report the binders of its parent: a new level starts its count at
-- the `varDecls` of the parent, and registration skips an ident that a live level already tracks
-- at the same position. The report comes at the outer `end`.
section
variable (parentUnused : Nat)

namespace NestedCount

#guard_msgs in
end NestedCount

/--
warning: variable 'parentUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end

-- `namespace A.B` opens two scopes, so `end A.B` pops two levels at once.
namespace MultiPopA.MultiPopB
variable (multiPopUnused : Nat)

/--
warning: variable 'multiPopUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
end MultiPopA.MultiPopB

-- The linter stays silent while the option is off.
section
set_option linter.unusedVariableCommand false
variable (optionOffNat : Nat)

#guard_msgs in
end

/-!
The two cases below are false negatives that the linter accepts. Usage matching is by name over
the whole command syntax, so any identifier with the name of a binder marks it as used. A name
test that skipped these would have to decide which occurrences resolve to the binder, and a
wrong answer there removes a live binder. The linter prefers a missed report to that.
-/

-- A local binder with the name of a section binder marks the section binder as used, although
-- no declaration of the scope uses the section binder.
section
variable (collide : Nat)

theorem collide_local (collide : Bool) : collide = collide := rfl

#guard_msgs in
end

-- An identifier of a proof body marks a binder as used, although the binder reaches no
-- statement of the scope.
section
variable (bodyName : Nat)

theorem body_names_it : True := by
  have bodyName : Nat := 0
  trivial

#guard_msgs in
end

-- A terminal command reports the binders of every open scope.
section
variable (eofUnused : Nat)

/--
warning: using 'exit' to interrupt Lean
---
warning: variable 'eofUnused' is never used in this scope

Note: This linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in
#exit

-- The report fires once per file: a second terminal command adds nothing.
/-- warning: using 'exit' to interrupt Lean -/
#guard_msgs in
#exit
