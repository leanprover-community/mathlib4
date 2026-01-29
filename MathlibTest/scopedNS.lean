import Mathlib.Tactic.ScopedNS
import Mathlib.Util.ParseCommand

namespace scopeNSTest

open Lean Elab.Command in

/-- helper command to display docstring -/
elab "#doc" x:ident : command => do
  if let some s ← findDocString? (← getEnv) (← liftCoreM do realizeGlobalConstNoOverload x) then
  logInfo m!"{s}"

scoped[Test] postfix:max (name := t₁) "ᵀ" => (Nat.add · 1)
scoped[Test] prefix:max (name := t₂) "ᵀᵀ" => Nat.add 1
scoped[Test] infix:max (name := t₃) "+|+" => Nat.add
scoped[Test] infixr:max (name := t₄) "-|-" => Nat.sub
scoped[Test] infixl:max (name := t₅) "*|*" => Nat.mul
scoped[Test] syntax (name := t₆) "-|-" term : term

-- Check that the node kind is registered such that `term_elab` can find it
@[term_elab Test.t₆]
def elabUpDown : Lean.Elab.Term.TermElab := fun _ _ => Lean.Elab.throwUnsupportedSyntax

/-- error: <input>:1:1: expected end of input -/
#guard_msgs in
#parse Lean.Parser.termParser.fn => "2ᵀ"

/-- info: Test.t₁ : Lean.TrailingParserDescr -/
#guard_msgs in
#check _root_.Test.t₁

/-- info: 3 -/
#guard_msgs in
open Test in
#eval 2ᵀ

open Test in
example (n : Nat) : nᵀ = ᵀᵀn := by
  dsimp only
  guard_target =ₛ Nat.add n 1 = Nat.add 1 n
  rw [Nat.add_eq, Nat.add_eq, Nat.add_comm]

/-- info: Test.t₂ : Lean.ParserDescr -/
#guard_msgs in #check _root_.Test.t₂
/-- info: Test.t₃ : Lean.TrailingParserDescr -/
#guard_msgs in #check _root_.Test.t₃
/-- info: Test.t₄ : Lean.TrailingParserDescr -/
#guard_msgs in #check _root_.Test.t₄
/-- info: Test.t₅ : Lean.TrailingParserDescr -/
#guard_msgs in #check _root_.Test.t₅

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
