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
warning: Command range: (426, 470).
Debt size: 1
[deprecated Nat (since := "")]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
@[deprecated Nat (since := "")] example := 0

/--
warning: Command range: (651, 693).
Debt size: 1
[deprecated (since := "")]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
@[deprecated (since := "")] alias X := Nat


/--
warning: Command range: (885, 928).
Debt size: 1
[set_option linter.deprecated false]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option linter.deprecated false in /-!-/

/--
warning: Command range: (1121, 1192).
Debt size: 1
[set_option linter.deprecated false]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option linter.deprecated false in
@[simp] example : True := trivial

namespace Fin.NatCast
def zero := 0
end Fin.NatCast

/--
warning: Command range: (1432, 1460).
Debt size: 1
[open Fin.NatCast hiding zero]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
open Fin.NatCast hiding zero

/--
warning: Command range: (1635, 1651).
Debt size: 1
[open Fin.NatCast]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
open Fin.NatCast


/--
warning: Command range: (1817, 1878).
Debt size: 1
[erw []]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
example : 0 = 0 := by
  rewrite [← Nat.add_zero 0]
  erw []

/--
warning: Command range: (2050, 2097).
Debt size: 1
[nolint simpNF]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
@[nolint simpNF]
example : True := by
  trivial


/--
warning: Command range: (2465, 2768).
Debt size: 5
[set_option backward.eqns.nonrecursive false,
 set_option backward.dsimp.proofs false,
 set_option synthInstance.maxHeartbeats 100,
 set_option maxHeartbeats 100,
 set_option tactic.skipAssignedInstances false]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option backward.eqns.nonrecursive false in
set_option backward.dsimp.proofs false in
set_option pp.proofs false in
set_option synthInstance.maxHeartbeats 100 in -- testing techDebtLinter
set_option maxHeartbeats 100 in -- testing techDebtLinter
set_option tactic.skipAssignedInstances false in /-!-/

/--
warning: Command range: (2952, 2974).
Debt size: 1
[#adaptation_note /-- -/
 ]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
#adaptation_note /---/

/--
warning: Command range: (3158, 3213).
Debt size: 1
[#adaptation_note /-- -/
 ]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
example : True := by
  #adaptation_note /---/
  trivial

/--
warning: Command range: (3443, 3516).
Debt size: 2
[set_option linter.style.longFile 0, set_option linter.style.longFile 10]

Note: This linter can be disabled with `set_option linter.techDebtLinter false`
-/
#guard_msgs in
set_option linter.style.longFile 0 in
set_option linter.style.longFile 10
