import Lean.Meta.Basic
import Mathlib.Tactic.Explode.Datatypes
import Mathlib.Tactic.Explode.Pretty
open Lean Elab Std
set_option linter.unusedVariables false

theorem my_theorem : ∀ (p : Prop), p → p :=
  λ (p : Prop) => (λ hP : p => hP)

partial def core : Expr → Bool → Nat → Entries → CoreM Entries
  | e@(Expr.lam varName varType body binderInfo), si, depth, entries => do
    dbg_trace "want _____0"

    -- varName => p
    -- varType => Prop
    -- body    => fun (hP : #0) => hP
    let m : FVarId ← mkFreshFVarId
    let l := Expr.fvar m

    let entry_1 : Entry := {
      expr   := l,
      line   := entries.size,
      depth  := depth,
      status := Status.sintro,
      thm    := Thm.name varName,
      deps   := []
    }
    dbg_trace entry_1

    -- we want to turn "fun (hP : #0) => hP" into "fun (hP : p) => hP"
    -- => fun (hP : p) => hP
    -- let body' := Expr.replaceFVar body (Expr.bvar 0) (Expr.const varName [])

    let body' := Expr.instantiate1 body l


    let entries_1 ← core body' si depth (entries.add entry_1)

    let entry_2 : Entry := {
      expr   := e,
      line   := entries_1.size,
      depth  := depth,
      status := Status.lam,
      thm    := Thm.string "∀I",
      deps   := [entries.size, entries_1.size - 1]
    }
    dbg_trace entry_2
    let entries_2 := entries_1.add entry_2
    return entries_2
  | e, si, depth, es => do
    dbg_trace "want _____1"
    -- filter e >>
    let args := Expr.getAppArgs e
    let f := Expr.getAppFn e
    match (f, args) with
      | (fn, #[]) =>
        dbg_trace "want _____2"
        let en : Entry := ⟨fn, es.size, depth, Status.reg, Thm.expr fn, []⟩
        dbg_trace en
        return (es.add en)
      | (fn, args) =>
        dbg_trace "nothing"
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

-- 1. Lean to infer the goddamn type
-- 2. And... move type inference from Pretty to core


-- OLD
-- 0│   │ p  ├ Prop
-- 1│   │ hP ├ p
-- 2│1,1│ ∀I │ p → p ---- this is the type we can't infer
-- 3│0,2│ ∀I │ ∀ (p : Prop), p → p


-- NEW
-- expr: _uniq.39621,                   line: 0, thm: p
-- expr: _uniq.39622,                   line: 1, thm: hP
-- expr: hP,                            line: 2, thm: e.toString todo
-- expr: fun (hP : p) => hP,            line: 3, thm: ∀I --- this
-- expr: fun (p : Prop) (hP : p) => hP, line: 4, thm: ∀I

-- NEW
-- formatMe: fun (p : Prop) (hP : p) => hP
-- formatted: forall (p : Prop), p -> p

-- formatMe: fun (hP : p) => hP

-- 1. Compose an expression `λ (hP : p) => hP` in OLD
-- 2. Try `tactic.infer_type ex` in OLD
-- 3. Compose an expression `λ (hP : p) => hP` in NEW
-- 4. Try `Lean.Meta.inferType ex` in NEW

-- def ex : Expr :=
--   Expr.lam `hP (Expr.fvar "hi")
--   (
--     Expr.lam `hP (Expr.bvar 0)
--     (Expr.bvar 1)
--     BinderInfo.default
--   )
--   BinderInfo.default


-- OLD
-- formatMe: λ (p : Prop) (hP : p), hP
-- formatted: ∀ (p : Prop), p → p

-- formatMe: λ (hP : p), hP
-- formatted: p → p

-- formatMe: hP
-- formatted: p

-- formatMe: p
-- formatted: Prop
