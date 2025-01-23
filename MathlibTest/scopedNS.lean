import Mathlib.Tactic.ScopedNS

namespace scopeNSTest

open Lean Elab.Command in

/-- helper command to display docstring -/
elab "#doc" x:ident : command => do
  if let some s ← findDocString? (← getEnv) (← liftCoreM do realizeGlobalConstNoOverload x) then
  logInfo m!"{s}"

scoped[Test] postfix:1024 (name := tt) "ᵀ" => Nat.add 1

-- TODO: is there something to guard a parsing error?
-- #check 2ᵀ

/-- info: Test.tt : Lean.TrailingParserDescr -/
#guard_msgs in
#check _root_.Test.tt

/-- info: 3 -/
#guard_msgs in
open Test in
#eval 2ᵀ


/-! ## Ensure bad syntax is not parsed -/

/--
error: This scoping directive conflicts with scoped[NS]
-/
#guard_msgs in
scoped[Test] local syntax "bla" : command

/--
error: This scoping directive conflicts with scoped[NS]
-/
#guard_msgs in
scoped[Test] scoped syntax "bla" : command

/--
error: unexpected docstring, move it in front of `scoped[NS]`!
-/
#guard_msgs in
scoped[Test] /-- I should not exist! -/ syntax "bla" : command

/--
error: unexpected attributes, move them in front of `scoped[NS]`!
-/
#guard_msgs in
scoped[Test] @[bad_place_for_attributes] syntax "bla" : command

/-! ## Test docstring -/

/-- this is a docstring -/
scoped[Test] syntax (name := updown) term " ↑↓ " term : term

/-- info: this is a docstring -/
#guard_msgs in
#doc _root_.Test.updown

/-- useless macro -/
scoped[Test] macro (name := theEnd) "◾" : term => `(term| by rfl)

/--
info: useless macro
-/
#guard_msgs in
#doc _root_.Test.theEnd

/-! ## Test attributes

TODO: what are sensible applications of attributes to these commands? add some
to replace this test. Further, check the
-/

/-- useless macro -/
@[simp]
scoped[Test] macro (name := theEndAgain) "◾" : term => `(term| by rfl)

/--
info: useless macro
-/
#guard_msgs in
#doc _root_.Test.theEnd

/--
warning: 'Test.theEnd' does not have [simp] attribute
-/
#guard_msgs in
attribute [-simp] Test.theEnd

#guard_msgs in
attribute [-simp] Test.theEndAgain

/-! ## Scoped attribute -/

-- TODO: add tests for `scoped[NS] attribute`.

scoped[Test] attribute [instance] Nat

end scopeNSTest
