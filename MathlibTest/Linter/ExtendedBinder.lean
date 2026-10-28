module

import Mathlib.Init

/-! Test the linter for `∀ᵉ`/`∃ᵉ` syntax. -/

set_option linter.style.extendedBinder true

/--
@ +1:10...28
warning: Try this:
  ∀ᵉ̵ (̵n > 0)̵,̲ (̵∀̲ ̲m > 0)̵

The basic `∀` syntax is preferred over `∀ᵉ`.
-/
#guard_msgs (positions := true) in
example : ∀ᵉ (n > 0) (m > 0), n + m > 1 := by grind

/--
@ +1:10...28
warning: Try this:
  ∃ᵉ̵ (̵n > 0)̵,̲ (̵∃̲ ̲m > 0)̵

The basic `∃` syntax is preferred over `∃ᵉ`.
-/
#guard_msgs (positions := true) in
example : ∃ᵉ (n > 0) (m > 0), n + m > 1 := by
  exists 1, by grind
  exists 1, by grind

/--
@ +1:0...6
info: ∀ (n : Nat), ∃ m, n = m : Prop
---
@ +1:13...23
warning: Try this:
  ∃ᵉ̵ m : Nat

The basic `∃` syntax is preferred over `∃ᵉ`.
---
@ +1:7...11
warning: Try this:
  ∀ᵉ̵ n

The basic `∀` syntax is preferred over `∀ᵉ`.
-/
#guard_msgs (positions := true) in
#check ∀ᵉ n, ∃ᵉ m : Nat, n = m
