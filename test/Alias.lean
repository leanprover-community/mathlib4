import Mathlib

namespace Alias

theorem foo : 1 + 1 = 2 := rfl
alias foo ← foo1 foo2 foo3
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

alias a_iff_a_and_a ↔ ..
example : True → True ∧ True := a_and_a_of_a True
example : True ∧ True → True := a_of_a_and_a True

end Alias
