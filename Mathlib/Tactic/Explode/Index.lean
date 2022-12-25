import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty

open Lean Elab
open Std

theorem my_theorem (p : Prop) : p → p :=
  λ (hP : p) => hP

def core : Expr → Bool → Nat → Entries → CoreM Entries
  | e@(Expr.lam varName varType body binderInfo), si, depth, entries => do
  --   -- varName => p
  --   -- varType => Prop
  --   -- body    => fun (hP : #0) => hP
  --   let m : FVarId ← mkFreshFVarId
  --   let l := Expr.fvar m
  --   -- we want to turn "fun (hP : #0) => hP" into "fun (hP : P) => hP"
  --  -- => fun (hP : p) => hP
  --   let body' := Expr.replaceFVar body (Expr.bvar 0) (Expr.const varName [])

  --   let entry_1 : Entry := {
  --     expr   := l,
  --     line   := entries.size,
  --     depth  := depth,
  --     status := Status.sintro,
  --     thm    := Thm.name varName,
  --     deps   := []
  --   }
  --   let entries_1 ← core body' si depth (entries.add entry_1)

  --   let entry_2 : Entry := {
  --     expr   := e,
  --     line   := entries_1.size,
  --     depth  := depth,
  --     status := Status.lam,
  --     thm    := Thm.string "∀I",
  --     deps   := [entries.size, entries_1.size - 1]
  --   }
  --   let entries_2 := entries_1.add entry_2
  --   return entries_2
    let entries1 := entries.add myEntry2
    let entries2 := entries1.add myEntry
    return entries2
  | a, b, c, d =>
    return entriesDefault

elab "#explode " theoremStx:ident : command => do
  let theoremName : Name ← resolveGlobalConstNoOverloadWithInfo theoremStx
  Lean.logInfo theoremName

  -- fun (p : Prop) (hP : p) => hP
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  Lean.logInfo body

  -- So now we have the body of the function, and we want to build the table from it
  -- let filter : String → String := λ smth => smth
  Elab.Command.liftCoreM do
    let results ← core body True 0 default
    Lean.Meta.MetaM.run' do
      let formatted : Format ← entriesToFormat results
      Lean.logInfo formatted

#explode my_theorem
