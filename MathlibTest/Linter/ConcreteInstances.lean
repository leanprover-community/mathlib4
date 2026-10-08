module

import Mathlib.Init

/--
@ +1:8...46
warning: There exists a global instance of type class `Add Nat`.
Please rely on this instance and remove the `[Add Nat]` assumption.

Note: This linter can be disabled with `set_option linter.concreteInstances false`
-/
#guard_msgs (positions := true) in
theorem test₁ [Add Nat] : 1 + 2 = 1 + 2 := rfl

/--
warning: The instance assumption `[Inv Nat]` does not contain free variables.
Instead of assuming it locally, please add a global instance with
`instance : Inv Nat := ...`

Note: This linter can be disabled with `set_option linter.concreteInstances false`
-/
#guard_msgs in
theorem test₂ [Inv Nat] : 2⁻¹ = 2⁻¹ := rfl

/--
warning: The instance assumption `[(α : Type) → Add α]` does not contain free variables.
Instead of assuming it locally, please add a global instance with
`instance : (α : Type) → Add α := ...`

Note: This linter can be disabled with `set_option linter.concreteInstances false`
-/
#guard_msgs in
theorem test₃ [∀ α, Add α] : 1 + 2 = 1 + 2 := rfl

-- Decidable hypotheses are exempt from the linter.
theorem test₄ [DecidableEq Prop] : True := trivial
theorem test₅ [∀ P, Decidable P] : True := trivial
theorem test₆ [∀ α, DecidableEq α] : True := trivial
