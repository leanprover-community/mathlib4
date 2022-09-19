/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Hanting Zhang
-/

import Mathlib.Lean.Expr.Basic
import Mathlib.Data.Fintype.Basic

open Lean.Meta

namespace Lean.Elab.Tactic

/-- If `e` is of the form `x ∈ (A : List α)` , `x ∈ (A : Finset α)`, or `x ∈ (A : Multiset α)`,
return `Some α`, otherwise `None`. -/
def getMemType {m : Type → Type} [Monad m] [MonadError m] (e : Expr) : m (Option Expr) := do
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, type, _, _, _]) =>
    match type.getAppFnArgs with
    | (``List, #[α])     => return α
    | (``Multiset, #[α]) => return α
    | (``Finset, #[α])   => return α
    | _ => throwError ("Hypothesis must be of type `x ∈ (A : List α)`, `x ∈ (A : Finset α)`,"
        ++ " or `x ∈ (A : Multiset α)`")
  | _ => return none

/--
Recursively runs the `cases` tactic on a hypothesis `h`,
as long as two goals are produced. `cases` is called recursively on the second goal,
and we return a list of the first goals which appeared.

This is useful for hypotheses of the form `h : a ∈ [l₁, l₂, ...]`,
which will be transformed into a sequence of goals with hypotheses `h : a = l₁`, `h : a = l₂`,
and so on.
-/
partial def unfoldCases (h : FVarId) : MVarId → MetaM (List MVarId) :=
fun g => do try
  let #[g₁, g₂] ← cases g h | throwError "unexpected number of cases"
  let gs ← unfoldCases g₂.fields[3]!.fvarId! g₂.mvarId
  return g₁.mvarId :: gs
catch _ => return []

/-- Implementation of the `fin_cases` tactic. -/
partial def finCasesAt (hyp : FVarId) : TacticM Unit := do
  withMainContext do
    let lDecl ←
      match (← getLCtx).find? hyp with
      | none => throwError m!"hypothesis not found"
      | some lDecl => pure lDecl
    match ← getMemType lDecl.type with
    | some _ => liftMetaTactic (unfoldCases hyp)
    | none =>
      -- Deal with `x : A`, where `[Fintype A]` is available:
      let inst ← synthInstance (← mkAppM ``Fintype #[lDecl.type])
      let elems ← mkAppOptM ``Fintype.elems #[lDecl.type, inst]
      let t ← mkAppM ``Membership.mem #[lDecl.toExpr, elems]
      let v ← mkAppOptM ``Fintype.complete #[lDecl.type, inst, lDecl.toExpr]

      let hyp ← liftMetaTacticAux fun mvarId => do
        let (fvar, mvarId) ← intro1P (← assert mvarId `this t v)
        pure (fvar, [mvarId])

      finCasesAt hyp

syntax (name := finCases) "fin_cases " ("*" <|> (term,+)) (" with " term)? : tactic

/- TODO: Implement the `with` clause. -/
/- TODO: use `norm_num` when there is no `with` clause. -/
/- TODO: can we name the cases generated according to their values,
   rather than `tail.tail.tail.head`? -/
/- TODO: copy across the tests from mathlib3. -/

@[tactic finCases] def evalFinCases : Tactic := fun stx =>
  match stx with
  | `(tactic| fin_cases $hyps,* $[with $es]?) => do
    for (h : TSyntax `term) in hyps.getElems do
      finCasesAt (← getFVarId h)
  | `(tactic| fin_cases * $[with $es]?) => do
    if es.getElems.size > 0 then
      throwError "Specify a single hypothesis when using a `with` argument."
    -- Try running `finCasesAt` on each local hypothesis.
    for h in (← getPropHyps) do
      finCasesAt h
  | _ => throwUnsupportedSyntax

example {p : Fin 4 → Prop} (i : Fin 4) (h : p i) : p i := by
  fin_cases i
  repeat exact h
