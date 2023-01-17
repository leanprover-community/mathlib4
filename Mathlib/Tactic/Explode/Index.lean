import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty
import Lean
open Lean Elab Std
set_option linter.unusedVariables false

theorem my_theorem : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)

partial def core : Expr → Bool → Nat → Entries → MetaM Entries
  | e@(Expr.lam varName varType body binderInfo), si, depth, entries => do
    Lean.logInfo "want _____0"

    Lean.Meta.withLocalDecl varName binderInfo varType λ x => do
      let expr1 := Expr.instantiate1 body x
      let context1 : MessageDataContext := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }

      let entry_1 : Entry := {
        expr   := x,
        type   := ← Lean.Meta.inferType x,
        line   := entries.size,
        depth  := depth,
        status := Status.sintro,
        thm    := Thm.name varName,
        deps   := [],
        context := context1
      }

      let entries_1 ← core expr1 si depth (entries.add entry_1)

      let entry_2 : Entry := {
        expr   := e,
        type   := ← Lean.Meta.inferType e,
        line   := entries_1.size,
        depth  := depth,
        status := Status.lam,
        thm    := Thm.string "∀I",
        deps   := [entries.size, entries_1.size - 1],
        context := context1
      }

      let entries_2 := entries_1.add entry_2
      return entries_2
  | e, si, depth, es => do
    Lean.logInfo "want _____1"

    let args := Expr.getAppArgs e
    let f := Expr.getAppFn e
    match (f, args) with
      | (fn, #[]) =>
        let en : Entry := ⟨fn, ← Lean.Meta.inferType fn, es.size, depth, Status.reg, Thm.expr fn, [], { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }⟩
        return es.add en
      | (fn, args) =>
        dbg_trace "nothing"
        return entriesDefault

elab "#explode " theoremStx:ident : command => do
  let theoremName : Name ← resolveGlobalConstNoOverloadWithInfo theoremStx
  -- Lean.logInfo theoremName
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  -- Lean.logInfo body

  -- So now we have the body of the function, and we want to build the table from it
  -- let filter : String → String := λ smth => smth
  Elab.Command.liftCoreM do
    Lean.Meta.MetaM.run' do
      let results ← core body True 0 default
      let formatted : MessageData ← entriesToMD results
      Lean.logInfo formatted

#explode my_theorem

-- OLD
-- 0│   │ p  ├ Prop
-- 1│   │ hP ├ p
-- 2│1,1│ ∀I │ p → p
-- 3│0,2│ ∀I │ ∀ (p : Prop), p → p

-- CURRENT
-- 3│0,2│ ∀I │ ∀ (p : Prop), p → p
-- 2│1,1│ ∀I │ p → p
-- 1│   │ hP ├ p
-- 0│   │ p  ├ Prop
