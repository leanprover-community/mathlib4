/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Util.CountHeartbeats

/-!
A linter that flags tactic `rfl`s that take over `10 ^ 5` heartbeats to elaborate.
-/

open Lean Elab Command

/-!
#  The "heavyRfl" linter

For "each" tactic `rfl`, the "heavyRfl" linter prints the number of heartbeats that it takes
to elaborate it, assuming that it exceeds the linter's value (set to `10 ^5` by default).
-/

namespace Mathlib.Linter

/-- The "heavyRfl" linter prints the number of heartbeat that a tactic `rfl` uses, if they exceed
the value of the linter option. -/
register_option linter.heavyRfl : Nat := {
  defValue := 10 ^ 5
  descr := "enable the heavyRfl linter"
}

def renameDecl (stxO : Syntax) (ns tail : Name) : (Option (Syntax × Name)) :=
  -- this allows the rename to work inside `open ... in ...`
  match stxO.find? (·.isOfKind ``Lean.Parser.Command.declaration) with
    | none => none
    | some stx =>
      match stx.find? (·.isOfKind ``Lean.Parser.Command.declId) with
      | none => some (stx, .anonymous)
      | some declId =>
        let id := declId[0]
        let declName := id.getId
        let newDeclName := ns ++ id.getId ++ tail
        let newId       := mkIdentFrom id newDeclName
        let newDeclId   := mkNode ``Lean.Parser.Command.declId #[newId, declId.getArgs.back]
        let new := stxO.replaceM (m := Id) (match · with
          | .node _ ``Lean.Parser.Command.declId _ => some newDeclId
          | .ident _ _ dName _ => if dName == declName then some newId else none
          | _ => none)
        some (new, newId.getId)

elab "rn" id:(ident)? cmd:command : command => do
  elabCommand cmd
  let id := id.getD (mkIdent `Hello)
  match renameDecl cmd .anonymous /-(← getCurrNamespace)-/ id.getId with
    | none => logInfo "no declaration name found"
    | some (d, n) =>
      logInfo m!"Name produced: '{n}'\n\nElaborating\n\n{d}"
      elabCommand d

end Mathlib.Linter

rn
open Nat in
def Nat.ST1Hello : Nat := zero
/-
Name produced: 'Nat.ST1.Hello'

Elaborating

-/

rn
open Nat in
def Nat.ST1 : Nat := zero

/--
info: Name produced: 'Nat.S.Hello'

Elaborating

def Nat.S.Hello (n : Nat) : Nat :=
  succ n
-/
#guard_msgs in
open Nat in
rn
def Nat.S (n : Nat) : Nat := succ n

namespace Mathlib.Linter

/--
info: Name produced: '[anonymous]'

Elaborating

instance : Add Nat :=
  ⟨Nat.add⟩
-/
#guard_msgs in
rn
instance : Add Nat := ⟨Nat.add⟩

/--
info: Name produced: 'X.Hello'

Elaborating

inductive X.Hello
  | id : Nat → X.Hello
-/
#guard_msgs in
rn
inductive X
  | id : Nat → X

namespace Y

/--
info: Name produced: 'XX.Hello'

Elaborating

@[simp, inline]
def XX.Hello : True :=
  .intro
-/
#guard_msgs in
rn
@[simp, inline]
def XX : True := .intro

/--
info: Name produced: '[anonymous]'

Elaborating

@[simp, inline]
instance : True :=
  .intro
-/
#guard_msgs in
rn
@[simp, inline]
instance : True := .intro

/--
info: Name produced: 'F.Hello'

Elaborating

@[simp, inline]
instance F.Hello : True :=
  .intro
-/
#guard_msgs in
rn
@[simp, inline]
instance F : True := .intro

/-- info: Mathlib.Linter.Y.XX.Hello : True -/
#guard_msgs in
#check Y.XX.Hello

namespace Int
/--
info: Name produced: 'Int.X.Hello'

Elaborating

theorem Int.X.Hello {n : Int} : 0 + n = n :=
  Int.zero_add ..
-/
#guard_msgs in
rn
theorem Int.X {n : Int} : 0 + n = n := Int.zero_add ..

namespace Mathlib.Linter

namespace HeavyRfl

@[inherit_doc Mathlib.Linter.linter.heavyRfl]
def heavyRflLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let hbBd ← getNatOption `linter.heavyRfl linter.heavyRfl.defValue
  unless hbBd != 0 do
    return
  if (← get).messages.hasErrors then
    return
  unless (stx.isOfKind ``Lean.Parser.Command.declaration) do return
  unless (stx.find? (·.isOfKind ``Lean.Parser.Tactic.tacticRfl)).isSome do return
  if (stx.find? (·.isOfKind `to_additive)).isSome then return
  if (stx.find? (·.isOfKind ``Lean.Parser.Term.namedArgument)).isSome then return
  let hbStx := Syntax.mkNumLit s!"{hbBd}"
  let declId :=
    (stx.find? (·.isOfKind ``Lean.Parser.Command.declId)).getD (mkNode `null #[mkIdent `ohHi])
  let declName    := declId[0].getId
  let newDeclName := ((← getScope).currNamespace ++ declName ++ `_hb)
  let newId       := mkIdentFrom declId[0] newDeclName
  let newDeclId   := mkNode ``Lean.Parser.Command.declId #[newId, declId.getArgs.back]
  let repl ← stx.replaceM fun s => do
    match s with
      | .node _ ``Lean.Parser.Tactic.tacticRfl _ =>
        return some (← `(tactic| count_heartbeats_over $hbStx ($(⟨s⟩); done)))
      | .node _ ``Lean.Parser.Command.declId _ =>
        return some newDeclId
      | .ident _ _ dName _ =>
        if dName == declName then return some newId else return none
      | _ => return none
--  withScope (fun sc => {sc with currNamespace := `X ++ sc.currNamespace}) do
  --logInfo repl
  let s ← get
  dbg_trace "Declaration '{(← getScope).currNamespace ++ declName}'"
  elabCommand repl
  set s

initialize addLinter heavyRflLinter

end HeavyRfl

end Mathlib.Linter
