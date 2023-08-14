import Mathlib.Util.InfoTree.Basic

open Lean Elab

/--
A helper structure containing a `TacticInfo` and `ContextInfo`,
along with children `InfoTree`s.

It is convenient to bundle these together because
many functions rely on both the `TacticInfo` and the `ContextInfo`.
-/
structure Lean.Elab.TacticInvocation where
  info : TacticInfo
  ctx : ContextInfo
  children : PersistentArray InfoTree

namespace Lean.Elab.TacticInvocation

/-- Return the range of the tactic, as a pair of file positions. -/
def range (t : TacticInvocation) : Position × Position := stxRange t.ctx.fileMap t.info.stx

/-- Pretty print a tactic. -/
def pp (t : TacticInvocation) : IO Format :=
  t.ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨t.info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

open Meta

/-- Run a tactic on the goals stored in a `TacticInvocation`. -/
def runMetaMGoalsBefore (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxBefore <| x t.info.goalsBefore

/-- Run a tactic on the after goals stored in a `TacticInvocation`. -/
def runMetaMGoalsAfter (t : TacticInvocation) (x : List MVarId → MetaM α) : IO α := do
  t.ctx.runMetaM {} <| Meta.withMCtx t.info.mctxAfter <| x t.info.goalsAfter

/-- Run a tactic on the main goal stored in a `TacticInvocation`. -/
def runMetaM (t : TacticInvocation) (x : MVarId → MetaM α) : IO α := do
  match t.info.goalsBefore.head? with
  | none => throw <| IO.userError s!"No goals at {← t.pp}"
  | some g => t.runMetaMGoalsBefore fun _ => do g.withContext <| x g

def mainGoal (t : TacticInvocation) : IO Expr :=
  t.runMetaM (fun g => do instantiateMVars (← g.getType))

def formatMainGoal (t : TacticInvocation) : IO Format :=
  t.runMetaM (fun g => do ppExpr (← instantiateMVars (← g.getType)))

def goalState (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsBefore (fun gs => gs.mapM fun g => do Meta.ppGoal g)

def goalStateAfter (t : TacticInvocation) : IO (List Format) := do
  t.runMetaMGoalsAfter (fun gs => gs.mapM fun g => do Meta.ppGoal g)

def ppExpr (t : TacticInvocation) (e : Expr) : IO Format :=
  t.runMetaM (fun _ => do Meta.ppExpr (← instantiateMVars e))

inductive Kind
| refl
| rw --(symm : Bool) (t : Term)
| exact (stx : Syntax) (e : Expr)
| apply (stx : Syntax) (e : Expr)
-- | refine
-- | convert
-- | have (n : Name) (ty : Expr) (v : Option Expr)
-- Feel free to add more as needed!
| other

instance : Inhabited Kind := ⟨.other⟩

def kind (t : TacticInvocation) : Kind :=
  match t.info.name? with
  | some ``Lean.Parser.Tactic.refl =>
    .refl
  | some ``Lean.Parser.Tactic.exact =>
    .exact
      t.info.stx.getArgs.toList.getLast! -- just the syntax for the term, don't include "exact"
      (t.children[0]?.bind InfoTree.ofExpr? |>.get!) -- the elaborated expression
  | some ``Lean.Parser.Tactic.apply =>
    -- TODO treat this with some scepticism; what happens if there is a configuration option?
    -- I haven't tested this at all.
    .apply
      t.info.stx.getArgs.toList.getLast! -- just the syntax for the term, don't include "exact"
      (t.children[0]?.bind InfoTree.ofExpr? |>.get!) -- the elaborated expression
  -- | some `Lean.Parser.Tactic.rwRule =>
  --   return .rw sorry sorry
  | _ =>  .other

end Lean.Elab.TacticInvocation
