import Batteries.Tactic.Alias
import Mathlib.Tactic.Linter.TechDebtLinter
--import Mathlib.adomaniLeanUtils.inspect_syntax

open _root_.Nat hiding add

open _root_.Nat

open _root_.Nat (add)

example : True := by
 open _root_.Nat in
 trivial

/--
warning: 1: [deprecated Nat (since := "")]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
@[deprecated Nat (since := "")] example := 0

/--
warning: 1: [deprecated (since := "")]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
@[deprecated (since := "")] alias X := Nat


/--
warning: 1: [set_option linter.deprecated false]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option linter.deprecated false in /-!-/

/--
warning: 1: [set_option linter.deprecated false]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option linter.deprecated false in
@[simp] example : True := trivial

namespace Fin.NatCast
def zero := 0
end Fin.NatCast

/--
warning: 1: [open Fin.NatCast hiding zero]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
open Fin.NatCast hiding zero

/--
warning: 1: [open Fin.NatCast]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
open Fin.NatCast


/--
warning: 1: [erw []]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
example : 0 = 0 := by
  rewrite [← Nat.add_zero 0]
  erw []

/--
warning: 1: [nolint simpNF]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
@[nolint simpNF]
example : True := by
  trivial


/--
warning: 3: [set_option backward.dsimp.proofs false, set_option maxHeartbeats 100, set_option tactic.skipAssignedInstances false]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option backward.dsimp.proofs false in
set_option pp.proofs false in
set_option maxHeartbeats 100 in -- testing techDebtLinter
set_option tactic.skipAssignedInstances false in /-!-/

/--
warning: 1: [#adaptation_note /-- -/
 ]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
#adaptation_note /---/

/--
warning: 1: [#adaptation_note /-- -/
 ]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
example : True := by
  #adaptation_note /---/
  trivial
