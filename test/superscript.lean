import Mathlib.Util.Superscript
import Mathlib.Tactic.UnsetOption

section

local syntax:arg term:max superscript(term) : term
local macro_rules | `($a:term $b:superscript) => `($a ^ $b)

variable (foo : Nat)
example : 2² = 4 := rfl
example : 2¹⁶ = 65536 := rfl
example (n : Nat) : n⁽²⁻¹⁾ ⁺ ⁶ /- not done yet... -/ ⁺ ᶠᵒᵒ = n ^ (7 + foo) := rfl
example : (fun n => 2ⁿ⁺¹) 15 = 2¹⁶ := rfl

end

section
local macro:arg a:term:max b:subscript(term) : term => `($a $(⟨b.raw[0]⟩))

example (a : Nat → Nat) (h : ∀ i, 1 ≤ (a)ᵢ) : 2 ≤ a ₀ + a ₁ :=
  Nat.add_le_add h₍₀₎ (h)₁

end
