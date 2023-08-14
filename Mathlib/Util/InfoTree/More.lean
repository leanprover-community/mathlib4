
import Mathlib.Util.Frontend
import Mathlib.Util.InfoTree.Basic

open Lean System



namespace Lean.Elab.InfoTree

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns a list of all results. -/
partial def findAllInfo (t : InfoTree) (ctx : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo × PersistentArray InfoTree) :=
  match t with
  | context ctx t => t.findAllInfo ctx p
  | node i ts  =>
      (if p i then [(i, ctx, ts)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx p)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`, and any children info trees. -/
def findTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo × PersistentArray InfoTree) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx, children) => (i, ctx, children)
  | _ => none

/--
Finds all tactic invocations in an `InfoTree`,
ignoring structuring tactics (e.g. `by`, `;`, multiline tactics, parenthesized tactics).
-/
def tactics (t : InfoTree) : List TacticInvocation :=
  t.findTacticNodes.map (fun ⟨i, ctx, children⟩ => ⟨i, ctx, children⟩)
    |>.filter TacticInvocation.substantive

end Lean.Elab.InfoTree

open Lean Elab

-- /-- Read the source code of the named module. -/
-- def moduleSource (mod : Name) : IO String := do
--   IO.FS.readFile (modToFilePath "." mod "lean")

def findLean (mod : Name) : IO FilePath := do
  return FilePath.mk ((← findOLean mod).toString.replace "build/lib/" "") |>.withExtension "lean"

/-- Read the source code of the named module. -/
def moduleSource (mod : Name) : IO String := do
  IO.FS.readFile (← findLean mod)

-- Building a cache is a bit ridiculous when
-- https://github.com/leanprover/lean4/issues/2408
-- prevents compiling multiple modules at all.
-- However, it does avoid error messages in the interpreter from attempting to recompile the same
-- module twice.

/-- Implementation of `compileModule`, which is the cached version of this function. -/
def compileModule' (mod : Name) : IO (Environment × List Message × List InfoTree) := do
  Lean.Elab.IO.processInput (← moduleSource mod) none {}

initialize compilationCache : IO.Ref <| HashMap Name (Environment × List Message × List InfoTree) ←
  IO.mkRef .empty

/--
Compile the source file for the named module, returning the
resulting environment, any generated messages, and all info trees.

The results are cached.
-/
def compileModule (mod : Name) : IO (Environment × List Message × List InfoTree) := do
  let m ← compilationCache.get
  match m.find? mod with
  | some r => return r
  | none => do
    let v ← compileModule' mod
    compilationCache.set (m.insert mod v)
    return v

/-- Compile the source file for the named module, returning all info trees. -/
def moduleInfoTrees (mod : Name) : IO (List InfoTree) := do
  let (_env, _msgs, trees) ← compileModule mod
  return trees

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
    ← (tactics.filter fun t => t.substantive && t.original).mapM
         fun t => do return (← t.goalState, ← t.pp))

def tacticsInDecl_format (mod? : Option Name) (decl : Name) : MetaM (List (List Format × Format)) := do
  -- Only report tactics with "original" syntax positions,
  -- as an approximation of the tactics that are there in the source code.
  let tactics := (← tacticsInDecl mod? decl).filter TacticInvocation.original
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
