import Lean
import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty
set_option linter.unusedVariables false
open Lean Elab Std

namespace Mathlib.Explode

-- TODO we don't use filter yet, let's add it later
def appendDep (entries : Entries) (expr : Expr) (deps : List Nat) : MetaM (List Nat) :=
  if let some existingEntry := entries.find expr then
    return existingEntry.line :: deps
  else
    return deps

mutual
partial def core : Expr → Bool → Nat → Entries → MetaM Entries
  | e@(Expr.lam varName varType body binderInfo), si, depth, entries => do
    dbg_trace "want _____0"

    Lean.Meta.withLocalDecl varName binderInfo varType λ x => do
      let context : MessageDataContext := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }

      let expr_1 := x
      let expr_2 := Expr.instantiate1 body x
      let expr_3 := e

      let entries_1 := entries.add {
        expr    := expr_1,
        type    := ← Lean.Meta.inferType expr_1,
        line    := entries.size,
        depth   := depth,
        status  := if si then Status.sintro else Status.intro,
        thm     := Thm.name varName,
        deps    := [],
        context := context
      }

      let entries_2 ← core expr_2 si (if si then depth else depth + 1) entries_1

      let entries_3 := entries_2.add {
        expr    := expr_3,
        type    := ← Lean.Meta.inferType expr_3,
        line    := entries_2.size,
        depth   := depth,
        status  := Status.lam,
        thm     := Thm.string "∀I",
        deps    := if si
          then [entries.size, entries_2.size - 1]
          -- In case of a "have" clause, the expr_2 here has an annotation
          else (← appendDep entries_2 expr_1 (← appendDep entries_2 expr_2.cleanupAnnotations []))
        context := context
      }

      return entries_3
  | e, si, depth, es => do
    let f := Expr.getAppFn e
    let args := Expr.getAppArgs e
    match (f, args) with
      -- Means we have a constant!
      | (nm@(Expr.const n _), args) =>
        dbg_trace "want _____1"
        -- dbg_trace nm -- And.intro
        -- Lean.logInfo nm
        return (← arguments e args.toList depth es (Thm.expr nm) [])
      | (fn, #[]) =>
        dbg_trace "want _____2"
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

        -- Lean.logInfo (toString es.size)
        -- Lean.logInfo (← Lean.Meta.inferType fn)

        -- TODO should be entries, check what's up with that and theorem_1
        -- I think this might be happening bc .add checks for the existence of this expr, and doesn't add the thing if it exists already.
        -- However adding it does look quite reasonable! (Once we adjust line ns and dependencies)
        return es
      | (fn, args) =>
        dbg_trace "FAKE want _____3"
        return entriesDefault
partial def arguments : Expr → List Expr → Nat → Entries → Thm → List Nat → MetaM Entries
  -- | e, ⟨arg::args⟩, depth, es, thm, deps => do
  | e, [], depth, es, thm, deps => do
    dbg_trace "args _____bbb"
    let context : MessageDataContext := { env := (← getEnv), mctx := {}, lctx := (← read).lctx, opts := {} }
    let entries := es.add {
      expr    := e,
      type    := ← Lean.Meta.inferType e,
      line    := es.size,
      depth   := depth,
      status  := Status.reg,
      thm     := thm,
      deps    := deps.reverse,
      context := context
    }
    return entries
  | e, arg::args, depth, es, thm, deps => do
    dbg_trace "args _____aaa"
    let es' ← core arg false depth es
    let deps' ← appendDep es' arg deps
    let entries ← arguments e args depth es' thm deps'
    return entries
end

end Mathlib.Explode

elab "#explode " theoremStx:ident : command => do
  let theoremName : Name ← resolveGlobalConstNoOverloadWithInfo theoremStx
  -- Lean.logInfo theoremName
  let body : Expr := ((← getEnv).find? theoremStx.getId).get!.value!
  -- Lean.logInfo body

  -- So now we have the body of the function, and we want to build the table from it
  -- let filter : String → String := λ smth => smth
  Elab.Command.liftCoreM do
    Lean.Meta.MetaM.run' do
      let results ← Mathlib.Explode.core body true 0 default
      let formatted : MessageData ← Mathlib.Explode.entriesToMD results
      Lean.logInfo formatted
