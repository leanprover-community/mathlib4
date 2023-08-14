import Lean

open Lean Elab

namespace Lean.Elab

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

namespace Lean.Elab.ContextInfo

def ppExpr (ctx : ContextInfo) (e : Expr) : IO Format :=
  ctx.runMetaM {} (do Meta.ppExpr (← instantiateMVars e))

end Lean.Elab.ContextInfo

namespace Lean.Elab.InfoTree

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

/-- Check if the info tree is the top level info tree for a declaration,
return it along with the declaration name if it is. -/
def elabDecl? (t : InfoTree) : Option (Name × InfoTree) :=
  match t.consumeContext with
  | .node (.ofCommandInfo i) c =>
    if i.elaborator == `Lean.Elab.Command.elabDeclaration
    then
      -- this is hacky: we are relying on the ordering of the child nodes.
      c.toList.foldr (fun cc acc => match (cc.consumeContext.ofName?, acc) with
                       | (_, some r) => some r
                       | (some n, none) => some (n, t)
                       | (none, none) => none )
                     none
    else
      none
  | _ => none

end Lean.Elab.InfoTree

def Lean.Elab.TacticInfo.name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

structure Lean.Elab.TacticInvocation where
  info : TacticInfo
  ctx : ContextInfo
  children : PersistentArray InfoTree

namespace Lean.Elab.TacticInvocation

def range (t : TacticInvocation) : Position × Position := stxRange t.ctx.fileMap t.info.stx

def pp (t : TacticInvocation) : IO Format :=
  t.ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨t.info.stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def name? (t : TacticInvocation) : Option Name :=
  t.info.name?

/-- Decide whether a tactic is "substantive", and actually transforms the goals
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def substantive (t : TacticInvocation) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some `Lean.Parser.Term.byTactic => false
  | some `Lean.Parser.Tactic.tacticSeq => false
  | some `Lean.Parser.Tactic.tacticSeq1Indented => false
  | some `Lean.Parser.Tactic.«tactic_<;>_» => false
  | some `Lean.Parser.Tactic.paren => false
  | _ => true

def original (t : TacticInvocation) : Bool :=
  match t.info.stx.getHeadInfo with
  | .original _ _ _ _  => true
  | _ => false

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

def kind (t : TacticInvocation) : Kind :=
  match t.name? with
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
