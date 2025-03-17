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
open Mathlib.Tactic.Superscript (subscriptable superscriptable)

private def check_subscript {α : Type} (_ : α) := ()
private def check_superscript {α : Type} (_ : α) := ()

@[app_delab check_subscript]
private def delabCheckSub : Delab := withOverApp 2 do
  let #[_, x] := (← getExpr).getAppArgs | failure
  let () ← withAppArg <| subscriptable x
  `("ok")

@[app_delab check_superscript]
private def delabCheckSuper : Delab := withOverApp 2 do
  let #[_, x] := (← getExpr).getAppArgs | failure
  let () ← withAppArg <| superscriptable x
  `("ok")

/-- `α` can not be subscripted or superscripted. -/
private def α {α : Type} {β : Type} : α → β → Unit := fun _ _ ↦ ()
/-- `β` can be both subscripted and superscripted. -/
private def β {α : Type} {β : Type} : α → β → Unit := fun _ _ ↦ ()

variable (n : String)

/-- info: "ok" : Unit -/
#guard_msgs in #check check_subscript (1234567890 == 1234567890)
/-- info: "ok" : Unit -/
#guard_msgs in #check check_subscript (β n (1 + 2 - 3 = 0))

/-- info: check_subscript (α 0 0) : Unit -/
#guard_msgs in #check check_subscript (α 0 0)

/-- info: "ok" : Unit -/
#guard_msgs in #check check_superscript (1234567890 == 1234567890)
/-- info: "ok" : Unit -/
#guard_msgs in #check check_superscript (β n (1 + 2 - 3 = 0))

/-- info: check_superscript (α 0 0) : Unit -/
#guard_msgs in #check check_superscript (α 0 0)

end delab
