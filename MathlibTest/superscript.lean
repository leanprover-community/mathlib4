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
local syntax:arg "#" noWs subscript(term) : term
local macro_rules | `(#$a:subscript) => `(check_subscript $a)

private def check_superscript {α : Type} (_ : α) := ()
local syntax:arg "#" noWs superscript(term) : term
local macro_rules | `(#$a:superscript) => `(check_superscript $a)

@[app_delab check_subscript]
private def delabCheckSubscript : Delab := withOverApp 2 do
  let #[_, e] := (← getExpr).getAppArgs | failure
  let sub ← withAppArg <| delabSubscript e
  `(#$sub:subscript)

@[app_delab check_superscript]
private def delabCheckSuperscript : Delab := withOverApp 2 do
  let #[_, e] := (← getExpr).getAppArgs | failure
  let sup ← withAppArg <| delabSuperscript e
  `(#$sup:superscript)

/-- `α` can not be subscripted or superscripted. -/
private def α {γ : Type} {δ : Type} : γ → δ → δ := fun _ ↦ id
/-- `β` can be both subscripted and superscripted. -/
private def β {γ : Type} {δ : Type} : γ → δ → δ := fun _ ↦ id

variable (n : String)

/-- info: #₁₂₃₄₅₆₇₈₉₀ ₌₌ ₁₂₃₄₅₆₇₈₉₀ : Unit -/
#guard_msgs in #check #₁₂₃₄₅₆₇₈₉₀ ₌₌ ₁₂₃₄₅₆₇₈₉₀
/-- info: #ᵦ ₙ ₍₁ ₊ ₂ ₋ ₃ ₌ ₀₎ : Unit -/
#guard_msgs in #check #ᵦ ₙ ₍₁ ₊ ₂ ₋ ₃ ₌ ₀₎
/-- info: #ᵦ : Unit -/
#guard_msgs in #check #ᵦ
/-- info: #ᵦ ₁ : Unit -/
#guard_msgs in #check #ᵦ ₁
/-- info: #ᵦ ᵦ ᵦ ᵦ : Unit -/
#guard_msgs in #check #ᵦ ᵦ ᵦ ᵦ

/-- info: check_subscript (α 0 0) : Unit -/
#guard_msgs in #check check_subscript (α 0 0)

/-- info: #¹²³⁴⁵⁶⁷⁸⁹⁰ ⁼⁼ ¹²³⁴⁵⁶⁷⁸⁹⁰ : Unit -/
#guard_msgs in #check #¹²³⁴⁵⁶⁷⁸⁹⁰ ⁼⁼ ¹²³⁴⁵⁶⁷⁸⁹⁰
/-- info: #ᵝ ⁿ ⁽¹ ⁺ ² ⁻ ³ ⁼ ⁰⁾ : Unit -/
#guard_msgs in #check #ᵝ ⁿ ⁽¹ ⁺ ² ⁻ ³ ⁼ ⁰⁾

-- partially-applied functions
/-- info: #ᵝ : Unit -/
#guard_msgs in #check #ᵝ
/-- info: #ᵝ ¹ : Unit -/
#guard_msgs in #check #ᵝ ¹
/-- info: #ᵝ ᵝ ᵝ ᵝ : Unit -/
#guard_msgs in #check #ᵝ ᵝ ᵝ ᵝ

/-- info: check_superscript (α 0 0) : Unit -/
#guard_msgs in #check check_superscript (α 0 0)

end delab
