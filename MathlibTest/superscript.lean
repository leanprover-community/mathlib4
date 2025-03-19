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

private def checkSubscript {α : Type} (_ : α) := ()
local syntax:arg "testsub(" noWs subscript(term) noWs ")" : term
local macro_rules | `(testsub($a:subscript)) => `(checkSubscript $a)

private def checkSuperscript {α : Type} (_ : α) := ()
local syntax:arg "testsup(" noWs superscript(term) noWs ")" : term
local macro_rules | `(testsup($a:superscript)) => `(checkSuperscript $a)

@[app_delab checkSubscript]
private def delabCheckSubscript : Delab := withOverApp 2 do
  let sub ← withAppArg delabSubscript
  `(testsub($sub:subscript))

@[app_delab checkSuperscript]
private def delabCheckSuperscript : Delab := withOverApp 2 do
  let sup ← withAppArg delabSuperscript
  `(testsup($sup:superscript))

universe u v

/-- `α` can not be subscripted or superscripted. -/
private def α {γ : Type u} {δ : Type v} : γ → δ → δ := fun _ ↦ id
/-- `β` can be both subscripted and superscripted. -/
private def β {γ : Type u} {δ : Type v} : γ → δ → δ := fun _ ↦ id

/-- `d` can not be subscripted, so we create an alias for `id`. -/
private abbrev ID {γ : Sort u} := @id γ

variable (n : Nat)

/-- info: checkSubscript testsub(₁) : Unit -/
#guard_msgs in #check checkSubscript (checkSubscript 1)
/-- info: checkSubscript testsup(¹) : Unit -/
#guard_msgs in #check checkSubscript (checkSuperscript 1)
/-- info: checkSuperscript testsup(¹) : Unit -/
#guard_msgs in #check checkSuperscript (checkSuperscript 1)
/-- info: checkSuperscript testsub(₁) : Unit -/
#guard_msgs in #check checkSuperscript (checkSubscript 1)

section subscript

/-- info: testsub(₁₂₃₄₅₆₇₈₉₀ ₌₌ ₁₂₃₄₅₆₇₈₉₀) : Unit -/
#guard_msgs in #check testsub(₁₂₃₄₅₆₇₈₉₀ ₌₌ ₁₂₃₄₅₆₇₈₉₀)
/-- info: testsub(ᵦ ₙ ₍₁ ₊ ₂ ₋ ₃ ₌ ₀₎) : Unit -/
#guard_msgs in #check testsub(ᵦ ₙ ₍₁ ₊ ₂ ₋ ₃ ₌ ₀₎)
/-- info: testsub(ᵦ) : Unit -/
#guard_msgs in #check testsub(ᵦ)
/-- info: testsub(ᵦ ₍₎) : Unit -/
#guard_msgs in #check testsub(ᵦ ₍₎)
/-- info: testsub(ᵦ ᵦ ᵦ ᵦ) : Unit -/
#guard_msgs in #check testsub(ᵦ ᵦ ᵦ ᵦ)
/-- info: testsub(ɪᴅ ɪᴅ ₃₇) : Unit -/
#guard_msgs in #check testsub(ɪᴅ ɪᴅ ₃₇)

end subscript

section superscript

/-- info: testsup(¹²³⁴⁵⁶⁷⁸⁹⁰ ⁼⁼ ¹²³⁴⁵⁶⁷⁸⁹⁰) : Unit -/
#guard_msgs in #check testsup(¹²³⁴⁵⁶⁷⁸⁹⁰ ⁼⁼ ¹²³⁴⁵⁶⁷⁸⁹⁰)
/-- info: testsup(ᵝ ⁿ ⁽¹ ⁺ ² ⁻ ³ ⁼ ⁰⁾) : Unit -/
#guard_msgs in #check testsup(ᵝ ⁿ ⁽¹ ⁺ ² ⁻ ³ ⁼ ⁰⁾)
/-- info: testsup(ᵝ) : Unit -/
#guard_msgs in #check testsup(ᵝ)
/-- info: testsup(ᵝ ⁽⁾) : Unit -/
#guard_msgs in #check testsup(ᵝ ⁽⁾)
/-- info: testsup(ᵝ ᵝ ᵝ ᵝ) : Unit -/
#guard_msgs in #check testsup(ᵝ ᵝ ᵝ ᵝ)
/-- info: testsup(ⁱᵈ ⁱᵈ ³⁷) : Unit -/
#guard_msgs in #check testsup(ⁱᵈ ⁱᵈ ³⁷)

end superscript

private def card {γ : Sort u} := @id γ
local prefix:arg "#" => card

private def factorial {γ : Sort u} := @id γ
local notation:10000 n "!" => factorial n

abbrev Nat' := Nat
def Nat'.γ : Nat' → Nat' := id

variable (n x_x : Nat')

section no_subscript

/-- info: checkSubscript x_x : Unit -/
#guard_msgs in #check checkSubscript x_x
/-- info: checkSubscript (α 0 0) : Unit -/
#guard_msgs in #check checkSubscript (α 0 0)
/-- info: checkSubscript (0 * 1) : Unit -/
#guard_msgs in #check checkSubscript (0 * 1)
/-- info: checkSubscript (0 ^ 1) : Unit -/
#guard_msgs in #check checkSubscript (0 ^ 1)
/-- info: checkSubscript [1] : Unit -/
#guard_msgs in #check checkSubscript [1]
/-- info: checkSubscript #n : Unit -/
#guard_msgs in #check checkSubscript #n
/-- info: checkSubscript 2! : Unit -/
#guard_msgs in #check checkSubscript 2!

/- The delaborator should reject dot notation. -/
open Nat' (γ) in
/-- info: checkSubscript n.γ : Unit -/
#guard_msgs in #check testsub(ᵧ ₙ)

/- The delaborator should reject metavariables. -/
set_option pp.mvars false in
/-- info: checkSubscript ?_ : Unit -/
#guard_msgs in #check checkSubscript ?_

/- The delaborator should reject because `n` is shadowed and `✝` can not be
subscripted. -/
variable {x} (hx : x = testsub(ₙ)) (n : True) in
/-- info: hx : x = checkSubscript n✝ -/
#guard_msgs in #check hx

end no_subscript

section no_superscript

/-- info: checkSuperscript x_x : Unit -/
#guard_msgs in #check checkSuperscript x_x
/-- info: checkSuperscript (α 0 0) : Unit -/
#guard_msgs in #check checkSuperscript (α 0 0)
/-- info: checkSuperscript (0 * 1) : Unit -/
#guard_msgs in #check checkSuperscript (0 * 1)
/-- info: checkSuperscript (0 ^ 1) : Unit -/
#guard_msgs in #check checkSuperscript (0 ^ 1)
/-- info: checkSuperscript [1] : Unit -/
#guard_msgs in #check checkSuperscript [1]
/-- info: checkSuperscript #n : Unit -/
#guard_msgs in #check checkSuperscript #n
/-- info: checkSuperscript 2! : Unit -/
#guard_msgs in #check checkSuperscript 2!

/- The delaborator should reject dot notation. -/
open Nat' (γ) in
/-- info: checkSuperscript n.γ : Unit -/
#guard_msgs in #check testsup(ᵞ ⁿ)

/- The delaborator should reject metavariables. -/
set_option pp.mvars false in
/-- info: checkSuperscript ?_ : Unit -/
#guard_msgs in #check checkSuperscript ?_

/- The delaborator should reject because `n` is shadowed and `✝` can not be
superscripted. -/
variable {x} (hx : x = testsup(ⁿ)) (n : True) in
/-- info: hx : x = checkSuperscript n✝ -/
#guard_msgs in #check hx

end no_superscript

end delab
