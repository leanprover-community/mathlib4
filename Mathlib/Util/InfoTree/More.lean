
import Mathlib.Util.Frontend
import Mathlib.Util.InfoTree.TacticInvocation.Basic


open Lean System


open Lean Elab IO


/-- Compiles the source file for the named module,
and returns a list containing the name and generated info tree for each declaration. -/
def moduleDeclInfoTrees (mod : Name) : IO (List (Name × InfoTree)) := do
  let trees ← moduleInfoTrees mod
  return trees.filterMap fun t => t.elabDecl?.map fun n => (n, t)

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
