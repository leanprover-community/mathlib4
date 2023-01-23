import Lean
import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty
set_option linter.unusedVariables false
open Lean Elab Std

namespace Mathlib.Explode

structure Opts where
  verbose : Bool

partial def core : Expr → Bool → Nat → Entries → Opts → MetaM Entries
  | e@(Expr.lam varName varType body binderInfo), si, depth, entries, opts => do
    if opts.verbose then dbg_trace "want _____0"
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

      let entries_2 ← core expr_2 si (if si then depth else depth + 1) entries_1 opts

      let entries_3 := entries_2.add {
        expr    := expr_3,
        type    := ← Lean.Meta.inferType expr_3,
        line    := entries_2.size,
        depth   := depth,
        status  := Status.lam,
        thm     := if (← Lean.Meta.inferType expr_3).isArrow
          then Thm.string "→I"
          else Thm.string "∀I",
        deps    := if si
          then [entries.size, entries_2.size - 1]
          else
            (← appendDep entries_2 expr_1
            -- In case of a "have" clause, the expr_2 here has an annotation
            (← appendDep entries_2 expr_2.cleanupAnnotations []))
        context := ← getContext
      }

      return entries_3
  | e@(Expr.app fn arg), si, depth, es, opts => do
    -- If we stumbled upon an application `f a b c`,
    -- don't just parse this one application, `a; b; c; f a; (f a) b; ((f a) b) c`
    -- lump them all under a single line! `a; b; c; f a b c`
    if !(← mayBeProof e) then return es

    let fn := Expr.getAppFn e
    let args := Expr.getAppArgs e
    match (fn, args) with
      | (fn, args) =>
        if opts.verbose then dbg_trace "want _____3"
        -- It's possible to turn this off if it's a .const and the theorem type is reaaally lengthy
        let entries_1 ← core fn.cleanupAnnotations false depth es opts

        let mut entries_2 := entries_1
        let mut deps_3 := []
        for arg in args do
          entries_2 ← core arg false depth entries_2 opts
          deps_3 ← appendDep entries_2 arg deps_3
        deps_3 ← appendDep entries_1 fn.cleanupAnnotations deps_3.reverse

        let entries_3 := entries_2.add {
          expr    := e,
          type    := ← Lean.Meta.inferType e,
          line    := entries_2.size,
          depth   := depth,
          status  := Status.reg,
          thm     := if fn.isConst
            then Thm.string s!"{fn.constName!}()"
            else Thm.string "∀E",
          deps    := deps_3,
          context := ← getContext
        }

        return entries_3
  | e@(Expr.letE declName type value body nonDep), si, depth, es, opts => do
    if opts.verbose then dbg_trace "auxilliary - strip .letE"
    core (reduceLets e) si depth es opts
  | e@(Expr.mdata _ expr), si, depth, es, opts => do
    if opts.verbose then dbg_trace "auxilliary - strip .mdata"
    core expr si depth es opts
  -- | e@(macro n l) si depth es :=
  --   trace "Auxilliary 3"
  --   explode.core l.head si depth es
  | e, si, depth, es, opts => do
    if opts.verbose then dbg_trace s!"default .{e.ctorName}"
    let entries := es.add {
      expr    := e,
      type    := ← Lean.Meta.inferType e,
      line    := es.size,
      depth   := depth,
      status  := Status.reg,
      thm     := if e.isConst
        then Thm.name e.constName!
        else Thm.string s!"{e}",
      deps    := [],
      context := ← getContext
    }
    return entries

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
      let results ← Mathlib.Explode.core body true 0 default { verbose := true }
      let formatted : MessageData ← Mathlib.Explode.entriesToMD results
      Lean.logInfo formatted

theorem theorem_7 (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  { intro h;
    cases h.right;
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inl ⟨h.left, ‹q›⟩ }
    { show (p ∧ q) ∨ (p ∧ r);
      exact Or.inr ⟨h.left, ‹r›⟩ } }
  { intro h;
    cases h;
    { show p ∧ (q ∨ r);
      rename_i hpq;
      exact ⟨hpq.left, Or.inl hpq.right⟩ }
    { show p ∧ (q ∨ r);
      rename_i hpr;
      exact ⟨hpr.left, Or.inr hpr.right⟩ } }


#explode theorem_7
