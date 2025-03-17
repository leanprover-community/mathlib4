import Mathlib.Util.Superscript
import Mathlib.Tactic.UnsetOption
import Lean.PrettyPrinter

section

local syntax:arg term:max noWs superscript(term) : term
local macro_rules | `($a:term$b:superscript) => `($a ^ $b)

variable (foo : Nat)
example : 2² = 4 := rfl
example : 2¹⁶ = 65536 := rfl
example (n : Nat) : n⁽²⁻¹⁾ ⁺ ⁶ /- not done yet... -/ ⁺ ᶠᵒᵒ = n ^ (7 + foo) := rfl
example : (fun n => 2ⁿ⁺¹) 15 = 2¹⁶ := rfl

/--
info: aⁱ
---
info: a³⁷
---
info: a⁽¹ ⁺ ¹⁾
-/
#guard_msgs in
run_cmd do
  let a := Lean.mkIdent `a
  let i := Lean.mkIdent `i
  Lean.logInfo <| ← `(term| $a$i:superscript)
  let lit ← `(term| 37)
  Lean.logInfo <| ← `(term| $a$lit:superscript)
  let one_plus_one ← `(term| (1 + 1))
  Lean.logInfo <| ← `(term| $a$one_plus_one:superscript)

-- TODO: fix this
/--
error: Not a superscript: 'α'
---
info: aα
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let a := Lean.mkIdent `a
  let α := Lean.mkIdent `α
  -- note: this only raises the error if we format non-lazily
  Lean.logInfo <| ← Lean.PrettyPrinter.ppTerm <| ← `(term| $a$α:superscript)

end

section
local macro:arg a:term:max b:subscript(term) : term => `($a $(⟨b.raw[0]⟩))

example (a : Nat → Nat) (h : ∀ i, 1 ≤ (a)ᵢ) : 2 ≤ a ₀ + a ₁ :=
  Nat.add_le_add h₍₀₎ (h)₁

/--
info: (a)ᵢ
---
info: (a)₃₇
---
info: (a)₍₁ ₊ ₁₎
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

/--
error: Not a subscript: 'α'
---
info: (a)α
-/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let a := Lean.mkIdent `a
  let α := Lean.mkIdent `α
  -- note: this only raises the error if we format non-lazily
  Lean.logInfo <| ← Lean.PrettyPrinter.ppTerm <| ← `(term| ($a)$α:subscript)

end

section delab

open Lean PrettyPrinter.Delaborator SubExpr
open Mathlib.Tactic (delabSubscript delabSuperscript)

private def check_subscript {α : Type} (_ : α) := ()
local syntax:arg "test(" noWs subscript(term) noWs ")" : term
local macro_rules | `(test($a:subscript)) => `(check_subscript $a)

private def check_superscript {α : Type} (_ : α) := ()
local syntax:arg "test(" noWs superscript(term) noWs ")" : term
local macro_rules | `(test($a:superscript)) => `(check_superscript $a)

@[app_delab check_subscript]
private def delabCheckSubscript : Delab := withOverApp 2 do
  let sub ← withAppArg <| delabSubscript
  `(test($sub:subscript))

@[app_delab check_superscript]
private def delabCheckSuperscript : Delab := withOverApp 2 do
  let sup ← withAppArg <| delabSuperscript
  `(test($sup:superscript))

universe u v

/-- `α` can not be subscripted or superscripted. -/
private def α {γ : Type u} {δ : Type v} : γ → δ → δ := fun _ ↦ id
/-- `β` can be both subscripted and superscripted. -/
private def β {γ : Type u} {δ : Type v} : γ → δ → δ := fun _ ↦ id

/-- `d` can not be subscripted, so we create an alias for `id`. -/
private abbrev ID {γ : Sort u} := @id γ

variable (n : String)

/-- info: test(₁₂₃₄₅₆₇₈₉₀ ₌₌ ₁₂₃₄₅₆₇₈₉₀) : Unit -/
#guard_msgs in #check test(₁₂₃₄₅₆₇₈₉₀ ₌₌ ₁₂₃₄₅₆₇₈₉₀)
/-- info: test(ᵦ ₙ ₍₁ ₊ ₂ ₋ ₃ ₌ ₀₎) : Unit -/
#guard_msgs in #check test(ᵦ ₙ ₍₁ ₊ ₂ ₋ ₃ ₌ ₀₎)
/-- info: test(ᵦ) : Unit -/
#guard_msgs in #check test(ᵦ)
/-- info: test(ᵦ ₍₎) : Unit -/
#guard_msgs in #check test(ᵦ ₍₎)
/-- info: test(ᵦ ᵦ ᵦ ᵦ) : Unit -/
#guard_msgs in #check test(ᵦ ᵦ ᵦ ᵦ)
/-- info: test(ɪᴅ ɪᴅ ₃₇) : Unit -/
#guard_msgs in #check test(ɪᴅ ɪᴅ ₃₇)

/-- info: check_subscript (α 0 0) : Unit -/
#guard_msgs in #check check_subscript (α 0 0)

/-- info: test(¹²³⁴⁵⁶⁷⁸⁹⁰ ⁼⁼ ¹²³⁴⁵⁶⁷⁸⁹⁰) : Unit -/
#guard_msgs in #check test(¹²³⁴⁵⁶⁷⁸⁹⁰ ⁼⁼ ¹²³⁴⁵⁶⁷⁸⁹⁰)
/-- info: test(ᵝ ⁿ ⁽¹ ⁺ ² ⁻ ³ ⁼ ⁰⁾) : Unit -/
#guard_msgs in #check test(ᵝ ⁿ ⁽¹ ⁺ ² ⁻ ³ ⁼ ⁰⁾)
/-- info: test(ᵝ) : Unit -/
#guard_msgs in #check test(ᵝ)
/-- info: test(ᵝ ⁽⁾) : Unit -/
#guard_msgs in #check test(ᵝ ⁽⁾)
/-- info: test(ᵝ ᵝ ᵝ ᵝ) : Unit -/
#guard_msgs in #check test(ᵝ ᵝ ᵝ ᵝ)
/-- info: test(ⁱᵈ ⁱᵈ ³⁷) : Unit -/
#guard_msgs in #check test(ⁱᵈ ⁱᵈ ³⁷)

/-- info: check_superscript (α 0 0) : Unit -/
#guard_msgs in #check check_superscript (α 0 0)

end delab
