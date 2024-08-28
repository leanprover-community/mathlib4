import Mathlib.Tactic.Linter.Lint
import Mathlib.Tactic.ToAdditive
import Mathlib.Order.SetNotation

-- TODO: the linter also runs on the #guard_msg, so disable it once
-- See https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/.23guard_msgs.20doesn't.20silence.20warnings/near/423534679

set_option linter.dupNamespace false

/--
warning: The namespace 'add' is duplicated in the declaration 'add.add'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
def add.add := True

namespace Foo

/--
warning: The namespace 'Foo' is duplicated in the declaration 'Foo.Foo.foo'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
def Foo.foo := True

-- the `dupNamespace` linter does not notice that `to_additive` created `Foo.add.add`.
#guard_msgs in
@[to_additive] theorem add.mul : True := .intro

--  However, the declaration `Foo.add.add` is present in the environment.
run_cmd Lean.Elab.Command.liftTermElabM do
  let decl := (← Lean.getEnv).find? ``Foo.add.add
  guard decl.isSome

namespace Nat

/--
warning: The namespace 'Nat' is duplicated in the declaration 'Foo.Nat.Nat.Nats'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
alias Nat.Nats := Nat

end Nat
end Foo

namespace add

/--
warning: The namespace 'add' is duplicated in the declaration 'add.add'
note: this linter can be disabled with `set_option linter.dupNamespace false`
-/
#guard_msgs in
set_option linter.dupNamespace true in
export Nat (add)

end add

set_option linter.cdot false in
/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
-/
#guard_msgs in
set_option linter.cdot true in
attribute [instance] Int.add in
instance : Inhabited Nat where
  default := by
    . have := 0
      · have : Nat → Nat → Nat := (· + .)
        . exact 0

set_option linter.cdot false in
/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.
note: this linter can be disabled with `set_option linter.cdot false`
-/
#guard_msgs in
set_option linter.cdot true in
example : Add Nat where add := (. + ·)

set_option linter.dollarSyntax false in
/--
warning: Please use '<|' instead of '$' for the pipe operator.
note: this linter can be disabled with `set_option linter.dollarSyntax false`
---
warning: Please use '<|' instead of '$' for the pipe operator.
note: this linter can be disabled with `set_option linter.dollarSyntax false`
-/
#guard_msgs in
set_option linter.dollarSyntax true in
attribute [instance] Int.add in
instance (f g : Nat → Nat) : Inhabited Nat where
  default := by
    · have := 0
      · have : Nat := f $ g $ 0
        · exact 0

section lambdaSyntaxLinter

set_option linter.style.lambdaSyntax false

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
example : ℕ → ℕ := λ _ ↦ 0

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
def foo : Bool := by
  let _f : ℕ → ℕ := λ _ ↦ 0
  exact true

example : ℕ → ℕ := fun n ↦ n - 1

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
example : ℕ → ℕ := by exact λ n ↦ 3 * n + 1

/--
warning: declaration uses 'sorry'
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
example : ℕ → ℕ → ℕ → ℕ := by
  have (n : ℕ) : True := trivial
  have : (Set.univ : Set ℕ) = ⋃ (i : ℕ), (Set.iUnion λ j ↦ ({0, j} : Set ℕ)) := sorry
  have : ∃ m : ℕ, ⋃ i : ℕ, (Set.univ : Set ℕ) = ∅ := sorry
  exact λ _a ↦ fun _b ↦ λ _c ↦ 0

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
example : True := by
  have : 0 = 0 ∧ 0 = 0 ∧ 1 + 3 = 4 := by
    refine ⟨by trivial, by
      let _f := λ n : ℕ ↦ 0;
      have : ℕ := by
        · -- comment
          · have := λ k : ℕ ↦ -5
            · exact 0
      refine ⟨by trivial, have := λ k : ℕ ↦ -5; by simp⟩
      ⟩
  trivial

-- Code such as the following would require walking the infotree instead:
-- the inner set_option is ignore (in either direction).
-- As this seems unlikely to occur by accident and its use is dubious, we don't worry about this.
/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.
note: this linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
example : ℕ → ℕ := set_option linter.style.lambdaSyntax false in λ _ ↦ 0

set_option linter.style.lambdaSyntax false
#guard_msgs in
example : ℕ → ℕ := set_option linter.style.lambdaSyntax true in λ _ ↦ 0

end lambdaSyntaxLinter

set_option linter.dollarSyntax false in
/--
warning: Please use '<|' instead of '$' for the pipe operator.
note: this linter can be disabled with `set_option linter.dollarSyntax false`
---
warning: Please use '<|' instead of '$' for the pipe operator.
note: this linter can be disabled with `set_option linter.dollarSyntax false`
-/
#guard_msgs in
set_option linter.dollarSyntax true in
attribute [instance] Int.add in
instance (f g : Nat → Nat) : Inhabited Nat where
  default := by
    · have := 0
      · have : Nat := f $ g $ 0
        · exact 0

set_option linter.longLine false
/--
warning: This line exceeds the 100 character limit, please shorten it!
note: this linter can be disabled with `set_option linter.longLine false`
-/
#guard_msgs in
set_option linter.longLine true in
/-!                                                                                                -/

#guard_msgs in
-- Lines with more than 100 characters containing URLs are allowed.
set_option linter.longLine true in
/-!  http                                                                                          -/

set_option linter.longLine true
-- The *argument* of `#guard_msgs` is *not* exempt from the linter.
/--
warning: This line exceeds the 100 character limit, please shorten it!
note: this linter can be disabled with `set_option linter.longLine false`
-/
#guard_msgs in                                                                            #guard true

-- However, the *doc-string* of #guard_msgs is exempt from the linter:
-- these are automatically generated, hence linting them is not helpful.
/--
info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
-/
#guard_msgs in
#eval List.range 27
