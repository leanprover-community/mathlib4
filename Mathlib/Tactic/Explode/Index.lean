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
      let context : MessageDataContext := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }

      let expr_1 := x
      let expr_2 := Expr.instantiate1 body x
      let expr_3 := e

      let entries_1 := entries.add {
        expr    := expr_1,
        type    := ← Lean.Meta.inferType x,
        line    := entries.size,
        depth   := depth,
        status  := Status.sintro,
        thm     := Thm.name varName,
        deps    := [],
        context := context
      }

      let entries_2 ← core expr_2 si depth entries_1

      let entries_3 := entries_2.add {
        expr    := expr_3,
        type    := ← Lean.Meta.inferType e,
        line    := entries_2.size,
        depth   := depth,
        status  := Status.lam,
        thm     := Thm.string "∀I",
        deps    := [entries.size, entries_2.size - 1],
        context := context
      }

      return entries_3
  | e, si, depth, es => do
    Lean.logInfo "want _____1"

    let args := Expr.getAppArgs e
    let f := Expr.getAppFn e
    match (f, args) with
      | (fn, #[]) =>

        let context : MessageDataContext := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }
        let entries := es.add {
          expr    := fn,
          type    := ← Lean.Meta.inferType fn,
          line    := es.size,
          depth   := depth,
          status  := Status.reg,
          thm     := Thm.expr fn,
          deps    := [],
          context := context
        }

        return entries
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
-- 0│   │ p  ├ Prop
-- 1│   │ hP ├ p
-- 2│1,1│ ∀I │ p → p
-- 3│0,2│ ∀I │ ∀ (p : Prop), p → p
