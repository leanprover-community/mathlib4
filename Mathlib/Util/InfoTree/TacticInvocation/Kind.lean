import Mathlib.Util.InfoTree.TacticInvocation.Basic
import Mathlib.Util.InfoTree.More

namespace Lean.Elab.TacticInvocation

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


open Lean Meta

/-- Find all goals which are discharged via the `rfl` tactic in the declaration `decl`. -/
def reflInDecl (mod? : Option Name) (decl : Name) : MetaM (List Expr) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match t.kind with
  | .refl => t.mainGoal
  | _ => return none

/-- Find all goals which are discharged via the `rfl` tactic in the declaration `decl`,
pretty printed as `Format` objects. -/
def reflInDecl_format (mod? : Option Name) (decl : Name) : MetaM (List Format) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match t.kind with
  | .refl => t.formatMainGoal
  | _ => return none

/-- Find all goals which are discharged via the `exact` tactic in the declaration `decl`.
Returns a list of triples consisting of a goal, syntax for the term, and elaborated term. -/
def exactInDecl (mod? : Option Name) (decl : Name) : MetaM (List (Expr × Syntax × Expr)) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match t.kind with
  | .exact stx e => return (← t.mainGoal, stx, e)
  | _ => return none

/-- Find all goals which are discharged via the `exact` tactic in the declaration `decl`.
Returns a list of formatted goals and terms used to discharge the goal. -/
def exactInDecl_format (mod? : Option Name) (decl : Name) : MetaM (List (Format × Format)) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match t.kind with
  | .exact _ e => return (← t.formatMainGoal, ← t.ppExpr e)
  | _ => return none

/-- Find all goals which are discharged via the `apply` tactic in the declaration `decl`.
Returns a list of triples consisting of a goal, syntax for the term, and elaborated term. -/
-- TODO we should also return information about generated subgoals.
def applyInDecl (mod? : Option Name) (decl : Name) : MetaM (List (Expr × Syntax × Expr)) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match t.kind with
  | .apply stx e => return (← t.mainGoal, stx, e)
  | _ => return none

/-- Find all goals which are discharged via the `apply` tactic in the declaration `decl`.
Returns a list of formatted goals and terms used to discharge the goal. -/
def applyInDecl_format (mod? : Option Name) (decl : Name) : MetaM (List (Format × Format)) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match t.kind with
  | .apply _ e => return (← t.formatMainGoal, ← t.ppExpr e)
  | _ => return none
