import Mathlib.Tactic.Linter.Style
import Mathlib.Order.SetNotation

/-! Tests for all the style linters. -/

/-! Tests for the `setOption` linter -/
section setOption
set_option linter.style.setOption true

-- All types of options are supported: boolean, numeric and string-valued.
-- On the top level, i.e. as commands.

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option pp.all true

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option profiler'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option profiler false

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option pp.all false

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option profiler.threshold'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option profiler.threshold 50

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option trace.profiler.output'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option trace.profiler.output "foo"

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option debug.moduleNameAtTimeout'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option debug.moduleNameAtTimeout false

-- The lint does not fire on arbitrary options.
set_option autoImplicit false

-- We also cover set_option tactics.

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
lemma tactic : True := by
  set_option pp.all true in
  trivial

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.raw.maxDepth'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
lemma tactic2 : True := by
  set_option pp.raw.maxDepth 32 in
  trivial

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option pp.all'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
lemma tactic3 : True := by
  set_option pp.all false in
  trivial

/--
warning: Setting options starting with 'debug', 'pp', 'profiler', 'trace' is only intended
for development and not for final code. If you intend to submit this contribution to the
Mathlib project, please remove 'set_option trace.profiler.output'.

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
lemma tactic4 : True := by
  set_option trace.profiler.output "foo" in
  trivial

-- This option is not affected, hence does not throw an error.
set_option autoImplicit true in
lemma foo' : True := trivial

-- TODO: add terms for the term form

/--
warning: Unscoped option maxHeartbeats is not allowed:
Please scope this to individual declarations, as in
```
set_option maxHeartbeats in
-- comment explaining why this is necessary
example : ... := ...
```

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option maxHeartbeats 20

#guard_msgs in
set_option maxHeartbeats 20 in
section
end

/--
warning: Unscoped option synthInstance.maxHeartbeats is not allowed:
Please scope this to individual declarations, as in
```
set_option synthInstance.maxHeartbeats in
-- comment explaining why this is necessary
example : ... := ...
```

Note: This linter can be disabled with `set_option linter.style.setOption false`
-/
#guard_msgs in
set_option synthInstance.maxHeartbeats 20

#guard_msgs in
set_option synthInstance.maxHeartbeats 20 in
section
end


end setOption

section cdotLinter
set_option linter.style.cdot true

set_option linter.globalAttributeIn false in
/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
-/
#guard_msgs in
attribute [instance] Int.add in
instance : Inhabited Nat where
  default := by
    . have := 0
      · have : Nat → Nat → Nat := (· + .)
        . exact 0

/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
-/
#guard_msgs in
example : Add Nat where add := (. + ·)

/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
-/
#guard_msgs in
example : Add Nat where add := (. + ·)

/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
---
warning: This central dot `·` is isolated; please merge it with the next line.

Note: This linter can be disabled with `set_option linter.style.cdot false`
---
warning: This central dot `·` is isolated; please merge it with the next line.

Note: This linter can be disabled with `set_option linter.style.cdot false`
-/
#guard_msgs in
example : Nat := by
  have : Nat := by
    ·
      -- some empty have
      have := 0
      ·

        -- another
        have := 1
        . exact 2
  exact 0

#guard_msgs in
example : True := by
  have : Nat := by
    -- This is how code should look: no error.
    · -- comment
      exact 37
  trivial

end cdotLinter
set_option linter.style.dollarSyntax true

set_option linter.globalAttributeIn false in
/--
warning: Please use '<|' instead of '$' for the pipe operator.

Note: This linter can be disabled with `set_option linter.style.dollarSyntax false`
---
warning: Please use '<|' instead of '$' for the pipe operator.

Note: This linter can be disabled with `set_option linter.style.dollarSyntax false`
-/
#guard_msgs in
attribute [instance] Int.add in
instance (f g : Nat → Nat) : Inhabited Nat where
  default := by
    · have := 0
      · have : Nat := f $ g $ 0
        · exact 0

section lambdaSyntaxLinter

set_option linter.style.lambdaSyntax true

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
example : ℕ → ℕ := λ _ ↦ 0

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
def foo : Bool := by
  let _f : ℕ → ℕ := λ _ ↦ 0
  exact true

example : ℕ → ℕ := fun n ↦ n - 1

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
example : ℕ → ℕ := by exact λ n ↦ 3 * n + 1

/--
warning: declaration uses 'sorry'
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
example : ℕ → ℕ → ℕ → ℕ := by
  have (n : ℕ) : True := trivial
  have : (Set.univ : Set ℕ) = ⋃ (i : ℕ), (Set.iUnion λ j ↦ ({0, j} : Set ℕ)) := sorry
  have : ∃ m : ℕ, ⋃ i : ℕ, (Set.univ : Set ℕ) = ∅ := sorry
  exact λ _a ↦ fun _b ↦ λ _c ↦ 0

/--
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
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

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
example : ℕ → ℕ := λ _ ↦ 0

set_option linter.style.lambdaSyntax false
#guard_msgs in
example : ℕ → ℕ := λ _ ↦ 0

end lambdaSyntaxLinter

set_option linter.style.longLine true
/--
warning: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
-/
#guard_msgs in
/-!                                                                                                -/

#guard_msgs in
-- Lines with more than 100 characters containing URLs are allowed.
/-!  http                                                                                          -/

set_option linter.style.longLine true
-- The *argument* of `#guard_msgs` is *not* exempt from the linter.
/--
warning: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
-/
#guard_msgs in                                                                            #guard true

-- However, the *doc-string* of #guard_msgs is exempt from the linter:
-- these are automatically generated, hence linting them is not helpful.
/--
info: [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]
-/
#guard_msgs in
#eval List.range 27

-- TODO: this used to error about the 100 character limit (mentioning string gaps),
-- restore this test!
/-- info: "                              \"                " : String -/
#guard_msgs in
#check "                              \"                \
                                                                  "

/- Tests for the `openClassical` linter -/
section openClassical

set_option linter.style.openClassical true

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Classical

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Nat Classical Nat

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Classical hiding choose

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Classical hiding choose axiomOfChoice

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Classical renaming choose -> foo, byCases -> bar

-- Only opening specific items.
/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Classical (choose)

-- `open scoped Classical` is also linted

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements
which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open scoped Classical

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
---
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open scoped Int Classical Nat Classical

-- `open ... in` is *not* linted.
#guard_msgs in
open Classical (choose) in
def bar : Nat := 1

#guard_msgs in
open scoped Classical in
def baz : Nat := 1

-- After one `open Classical` statement, the linter does not fire on subsequent declarations.

/--
warning: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
For theorem statements, either add missing decidability assumptions or use `open Classical in`.

Note: This linter can be disabled with `set_option linter.style.openClassical false`
-/
#guard_msgs in
open Classical

#guard_msgs in
def aux : Nat := 1

#guard_msgs in
def aux' : Nat := 1

end openClassical

/- Tests for the `show` linter -/
section showLinter

set_option linter.style.show true

-- The linter doesn't complain if the goal stays the same

#guard_msgs in
example : 1 + 2 = 3 := by
  show 1 + 2 = 3
  rfl

-- Binder names are ignored

#guard_msgs in
example : ∀ a : Nat, a = a := by
  show ∀ b : Nat, b = b
  intro
  rfl

-- Goal changes are linted

/--
warning: The `show` tactic should only be used to indicate intermediate goal states for readability.
However, this tactic invocation changed the goal. Please use `change` instead for these purposes.

Note: This linter can be disabled with `set_option linter.style.show false`
-/
#guard_msgs in
example : (fun a => a) 1 = 1 := by
  show 1 = 1
  rfl

-- Assigning meta-variables in the goal is also linted

/--
warning: The `show` tactic should only be used to indicate intermediate goal states for readability.
However, this tactic invocation changed the goal. Please use `change` instead for these purposes.

Note: This linter can be disabled with `set_option linter.style.show false`
-/
#guard_msgs in
example := by
  show 1 = 1
  rfl

end showLinter
