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

set_option pp.rawOnError true in
/--
info: (a)ᵢ
---
info: (a)₃₇
---
info: (a)₍₁ ₊ ₁₎
---
info: [Error pretty printing syntax: Not a superscript: 'α✝'. Falling back to raw printer.]
(term__._@.test.superscript._hyg.272 (Term.paren "(" `a ")") (Mathlib.Tactic.subscript `α._@.test.superscript._hyg.514))
-/
#guard_msgs in
run_cmd do
  let a := Lean.mkIdent `a
  let i := Lean.mkIdent `i
  Lean.logInfo <| ← `(term| ($a)$i:subscript)
  let lit ← `(term| 37)
  Lean.logInfo <| ← `(term| ($a)$lit:subscript)
  let one_plus_one ← `(term| (1 + 1))
  Lean.logInfo <| ← `(term| ($a)$one_plus_one:subscript)
  let ohno ← `(α)
  Lean.logInfo <| ← `(term| ($a)$ohno:subscript)

end
