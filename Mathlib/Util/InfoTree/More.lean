
import Mathlib.Util.Frontend
import Mathlib.Util.InfoTree.TacticInvocation

open Lean System

namespace Lean.Elab.InfoTree

/--
Finds all tactic invocations in an `InfoTree`,
ignoring structuring tactics (e.g. `by`, `;`, multiline tactics, parenthesized tactics).
-/
def tactics (t : InfoTree) : List TacticInvocation :=
  t.findTacticNodes.map (fun ⟨i, ctx, children⟩ => ⟨i, ctx, children⟩)
    |>.filter fun i => i.info.isSubstantive

end Lean.Elab.InfoTree

open Lean Elab IO


/-- Compiles the source file for the named module,
and returns a list containing the name and generated info tree for each declaration. -/
def moduleDeclInfoTrees (mod : Name) : IO (List (Name × InfoTree)) := do
  let trees ← moduleInfoTrees mod
  return trees.filterMap InfoTree.elabDecl?

/-- Compile the source file for the named module,
and return the info tree generated for the specified declaration. -/
def declInfoTree (mod? : Option Name) (decl : Name) : MetaM InfoTree := do
  let mod ← match mod? with
  | some _ => pure mod?
  | none => findModuleOf? decl
  match mod with
  | none => throwError s!"Could not determine the module {decl} was declared in."
  | some m =>
      let r ← moduleDeclInfoTrees m
      match r.find? fun p => p.1 = decl with
      | none => throwError s!"Did not find InfoTree for {decl} in {m}!"
      | some (_, t) => return t

open Lean.Elab

def moduleDeclInfoTrees_format (mod : Name) : IO (List Format) := do
  let trees ← moduleDeclInfoTrees mod
  trees.mapM fun (n, t) => do return format (n, ← t.format)

def allTacticsInModule (mod : Name) : CoreM (List (Name × List TacticInvocation)) := do
  let trees ← moduleDeclInfoTrees mod
  return trees.map fun (n, t) => (n, t.tactics)

def allTacticsInModule_format (mod : Name) : CoreM (List (Name × List (Format × Format))) := do
  let r ← allTacticsInModule mod
  r.mapM fun (n, t) => do return (n, ← t.mapM fun i => do return (format i.info.stx, ← i.pp))

def tacticsInDecl (mod? : Option Name) (decl : Name) : MetaM (List TacticInvocation) := do
  let tree ← declInfoTree mod? decl
  return tree.tactics

def tacticsInModule_format (mod : Name) : MetaM (List (Name × List (List Format × Format))) := do
  (← allTacticsInModule mod).mapM fun (n, tactics) => do return (n,
    ← (tactics.filter fun t => t.info.isSubstantive && (Info.ofTacticInfo t.info).isOriginal).mapM
         fun t => do return (← t.goalState, ← t.pp))

def tacticsInDecl_format (mod? : Option Name) (decl : Name) : MetaM (List (List Format × Format)) := do
  -- Only report tactics with "original" syntax positions,
  -- as an approximation of the tactics that are there in the source code.
  let tactics := (← tacticsInDecl mod? decl).filter (fun t => (Info.ofTacticInfo t.info).isOriginal)
  tactics.mapM fun t => do return (← t.goalState, ← t.pp)

open Meta

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
