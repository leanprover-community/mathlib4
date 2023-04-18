
import Mathlib.Util.Frontend

open Lean System

namespace Lean.Elab

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

structure Lean.Elab.TacticInvocation where
  info : TacticInfo
  ctx : ContextInfo

namespace Lean.Elab.TacticInvocation

def range (t : TacticInvocation) : Position × Position := stxRange t.ctx.fileMap t.info.stx

def pp (t : TacticInvocation) : IO Format :=
  t.ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨t.info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def name (t : TacticInvocation) : Option Name :=
  match t.info.stx with
  | Syntax.node _ n _ => some n
  | _ => none

def substantive (t : TacticInvocation) : Bool :=
  match t.name with
  | none => false
  | some `Lean.Parser.Term.byTactic => false
  | some `Lean.Parser.Tactic.tacticSeq => false
  | some `Lean.Parser.Tactic.tacticSeq1Indented => false
  | some `Lean.Parser.Tactic.«tactic_<;>_» => false
  | some `Lean.Parser.Tactic.paren => false
  | _ => true

#print Lean.Parser.Tactic.rwRule

inductive Kind
| refl (ty : Expr)
| rw (symm : Bool) (t : Term)
-- | exact
-- | apply
-- | refine
-- | convert
-- | have (n : Name) (ty : Expr) (v : Option Expr)
-- Feel free to add more as needed!
| other
deriving BEq

open Meta

def kind (t : TacticInvocation) : IO Kind :=
  match t.name with
  | some `Lean.Parser.Tactic.refl =>
    .refl <$> t.ctx.runMetaM {} t.info.goalsBefore.head!.getType
  -- | some `Lean.Parser.Tactic.rwRule =>
  --   return .rw sorry sorry
  | _ => pure .other

end Lean.Elab.TacticInvocation

namespace Lean.Elab.InfoTree

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns all results. -/
partial def findAllInfo (t : InfoTree) (ctx : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo) :=
  match t with
  | context ctx t => t.findAllInfo ctx p
  | node i ts  => (if p i then [(i, ctx)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx p)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree` corresponding to tactics,
each equipped with its relevant `ContextInfo`. -/
def findTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
    | .ofTacticInfo _ => true
    | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx) => (i, ctx)
  | _ => none




/--
Finds all tactic invocations in an `InfoTree`/
-/
def tactics (t : InfoTree) : List TacticInvocation :=
  t.findTacticNodes.map (fun ⟨i, ctx⟩ => ⟨i, ctx⟩)
    |>.filter TacticInvocation.substantive

/-- Discard any enclosing `InfoTree.context` layers. -/
def consumeContext : InfoTree → InfoTree
  | .context _ t => t.consumeContext
  | t => t

/-- Is this `InfoTree` a `TermInfo` for some `Expr`? -/
def ofExpr? (i : InfoTree) : Option Expr := match i with
  | .node (.ofTermInfo i) _ => some i.expr
  | _ => none

/-- Is this `InfoTree` a `TermInfo` for some `Name`? -/
def ofName? (i : InfoTree) : Option Name := i.ofExpr?.bind Expr.constName?

def elabDecl? (t : InfoTree) : Option (Name × InfoTree) :=
  match t.consumeContext with
  | .node (.ofCommandInfo i) c => if i.elaborator == `Lean.Elab.Command.elabDeclaration then
      -- this is hacky: we are relying on the ordering of the child nodes.
      match c.toList.getLast? with
      | some r => match r.consumeContext.ofName? with
        | some n => some (n, t)
        | none => none
      | none => none
    else
      none
  | _ => none

end Lean.Elab.InfoTree

open Lean Elab

def moduleSource (mod : Name) : IO String := do
  IO.FS.readFile (modToFilePath "." mod "lean")

def compileModule' (mod : Name) : IO (Environment × List Message × List InfoTree) := do
  Lean.Elab.IO.processInput (← moduleSource mod) none {}

initialize compilationCache : IO.Ref <| HashMap Name (Environment × List Message × List InfoTree) ←
  IO.mkRef .empty

def compileModule (mod : Name) : IO (Environment × List Message × List InfoTree) := do
  let m ← compilationCache.get
  match m.find? mod with
  | some r => return r
  | none => do
    let v ← compileModule' mod
    compilationCache.set (m.insert mod v)
    return v

def moduleInfoTrees (mod : Name) : IO (List InfoTree) := do
  let (_env, _msgs, trees) ← compileModule mod
  return trees

def moduleInfoTrees' (mod : Name) : IO (List Format) := do
  let (_env, _msgs, trees) ← compileModule mod
  trees.mapM fun t => t.format

/-- Compiles the source file for the named module,
and returns a list containing the name and generated info tree for each declaration. -/
def moduleDeclInfoTrees (mod : Name) : IO (List (Name × InfoTree)) := do
  let trees ← moduleInfoTrees mod
  return trees.filterMap InfoTree.elabDecl?

def declInfoTree (mod? : Option Name) (decl : Name) : MetaM InfoTree := do
  let mod ← match mod? with
  | some _ => pure mod?
  | none => findModuleOf? decl
  match mod with
  | none => throwError s!"Could not determine the module {decl} was declared in."
  | some m =>
      let r ← moduleDeclInfoTrees m
      match r.find? fun p => p.1 = decl with
      -- match r.head? with
      | none => throwError s!"Did not find InfoTree for {decl} in {m}!"
      | some (_, t) => return t

open Lean.Elab

def moduleDeclInfoTrees' (mod : Name) : IO (List Format) := do
  let trees ← moduleDeclInfoTrees mod
  trees.mapM fun (n, t) => do return format (n, ← t.format)

def allTacticsInModule (mod : Name) : CoreM (List (Name × List TacticInvocation)) := do
  let trees ← moduleDeclInfoTrees mod
  return trees.map fun (n, t) => (n, t.tactics)

def allTacticsInModule' (mod : Name) : CoreM (List (Name × List (Format × Format))) := do
  let r ← allTacticsInModule mod
  r.mapM fun (n, t) => do return (n, ← t.mapM fun i => do return (format i.info.stx, ← i.pp))

def tacticsInDecl (mod? : Option Name) (decl : Name) : MetaM (List TacticInvocation) := do
  let tree ← declInfoTree mod? decl
  return tree.tactics

def reflInDecl (mod? : Option Name) (decl : Name) : MetaM (List Expr) := do
  (← tacticsInDecl mod? decl).filterMapM fun t => do match ← t.kind with
  | .refl ty => return some ty
  | _ => return none
