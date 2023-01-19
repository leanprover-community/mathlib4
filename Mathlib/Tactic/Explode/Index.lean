import Lean
import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty
set_option linter.unusedVariables false
open Lean Elab Std

namespace Mathlib.Explode

mutual
partial def core : Expr → Bool → Nat → Entries → MetaM Entries
  | e@(Expr.lam varName varType body binderInfo), si, depth, entries => do
    dbg_trace "want _____0"

    Lean.Meta.withLocalDecl varName binderInfo varType λ x => do

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
        context := ← getContext
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
        context := ← getContext
      }

      return entries_3
  | e, si, depth, es => do
    let f := Expr.getAppFn e
    let args := Expr.getAppArgs e
    match (f, args) with
      | (nm@(Expr.const n _), args) =>
        dbg_trace "want _____1"
        return (← arguments e args.toList depth es (Thm.expr nm) [])
      | (fn, #[]) =>
        dbg_trace "want _____2"

        let entries := es.add {
          expr    := fn,
          type    := ← Lean.Meta.inferType fn,
          line    := es.size,
          depth   := depth,
          status  := Status.reg,
          thm     := Thm.expr fn,
          deps    := [],
          context := ← getContext
        }

        return entries
      | (fn, args) =>
        dbg_trace "want _____3"
        let entries_1 ← core fn false depth es
        -- In case of a "have" clause, the fn here has an annotation
        let deps ← appendDep entries_1 fn.cleanupAnnotations []
        let entries_2 ← arguments e args.toList depth entries_1 (Thm.string "∀E") deps
        return entries_2
partial def arguments : Expr → List Expr → Nat → Entries → Thm → List Nat → MetaM Entries
  | e, arg::args, depth, es, thm, deps => do
    dbg_trace "args _____aaa"
    let es' ← core arg false depth es
    -- TODO i think this might give us a wrong reference number
    -- if we had an expression with the same type previously
    let deps' ← appendDep es' arg deps
    let entries ← arguments e args depth es' thm deps'
    return entries
  | e, [], depth, es, thm, deps => do
    dbg_trace "args _____bbb"

    let entries := es.add {
      expr    := e,
      type    := ← Lean.Meta.inferType e,
      line    := es.size,
      depth   := depth,
      status  := Status.reg,
      thm     := thm,
      deps    := deps.reverse,
      context := ← getContext
    }
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

-- #explode theorem_4
