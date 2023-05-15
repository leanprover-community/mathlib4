import Mathlib.Tactic.Alias
import Mathlib.Tactic.RunCmd
import Std.Tactic.GuardExpr

open Lean Meta
namespace Alias
namespace A

/-- doc string for foo -/
theorem foo : 1 + 1 = 2 := rfl

/-- doc string for `alias foo` -/
alias foo ← foo1 foo2 foo3 _root_.B.foo4

example : 1 + 1 = 2 := foo1
example : 1 + 1 = 2 := foo2
example : 1 + 1 = 2 := foo3

def bar : Nat := 5
alias bar ← bar1 bar2
example : bar1 = 5 := rfl
example : bar2 = 5 := rfl

theorem baz (x : Nat) : x = x := rfl
alias baz ← baz1
example : 3 = 3 := baz1 3

theorem ab_iff_ba {t : Type} {a b : t} : a = b ↔ b = a := Iff.intro Eq.symm Eq.symm
alias ab_iff_ba ↔ ba_of_ab ab_of_ba
example {a b : Nat} : a = b → b = a := ba_of_ab
example {t : Type} {a b : t} : b = a → a = b := ab_of_ba

theorem a_iff_a_and_a (a : Prop) : a ↔ a ∧ a :=
  Iff.intro (λ x => ⟨x,x⟩) (λ x => x.1)

alias a_iff_a_and_a ↔ forward _
alias a_iff_a_and_a ↔ _ backward

example : True → True ∧ True := forward True
example : True ∧ True → True := backward True

/-- doc string for `alias a_iff_a_and_a` -/
alias a_iff_a_and_a ↔ ..
example : True → True ∧ True := a_and_a_of_a True
example : True ∧ True → True := a_of_a_and_a True

end A

-- test namespacing
example : 1 + 1 = 2 := A.foo1
example : 1 + 1 = 2 := B.foo4
example : True → True ∧ True := A.a_and_a_of_a True
example : True → True ∧ True := A.forward True
example : True ∧ True → True := A.backward True

namespace C

alias A.a_iff_a_and_a ↔ _root_.B.forward2 _
alias A.a_iff_a_and_a ↔ _ _root_.B.backward2

end C

example : True → True ∧ True := B.forward2 True
example : True ∧ True → True := B.backward2 True

theorem checkType : 1 + 1 = 2 ↔ 2 = 2 := .rfl
alias checkType ↔ forward backward

example : True := by
  have h1 := forward
  have h2 := backward
  guard_hyp h1 :ₛ 1 + 1 = 2 → 2 = 2
  guard_hyp h2 :ₛ 2 = 2 → 1 + 1 = 2
  trivial

def foo : ℕ → ℕ := id

alias foo ← bar

def baz (n : ℕ) := bar n

end Alias
