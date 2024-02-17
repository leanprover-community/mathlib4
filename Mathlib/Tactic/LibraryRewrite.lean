import Lean
import ProofWidgets
import Mathlib.Lean.Meta.RefinedDiscrTree.RefinedDiscrTree
import Aesop.Util.Basic

namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta Server

/-- The structure that is stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  name : Name
  symm : Bool
  numParams : Nat
deriving BEq, Inhabited

def RewriteLemma.length (rwLemma : RewriteLemma) : Nat :=
  rwLemma.name.toString.length

/--
We sort lemmata by the following conditions in order:
- left-to-right rewrites come first
- number of parameters
- length of the name
- alphabetical order
-/
def RewriteLemma.lt (a b : RewriteLemma) : Bool :=
  !a.symm && b.symm || a.symm == b.symm &&
    (a.numParams < b.numParams || a.numParams == b.numParams &&
      (a.length < b.length || a.length == b.length &&
        Name.lt a.name b.name))

instance : LT RewriteLemma := ⟨fun a b => RewriteLemma.lt a b⟩
instance (a b : RewriteLemma) : Decidable (a < b) :=
  inferInstanceAs (Decidable (RewriteLemma.lt a b))

def RewriteLemma.diffs (rwLemma : RewriteLemma) : Lean.AssocList SubExpr.Pos Widget.DiffTag :=
  let eqnPos := rwLemma.numParams.fold (init := SubExpr.Pos.root) fun _ => .pushBindingBody
  let lhsPos := eqnPos.pushAppFn.pushAppArg
  let rhsPos := eqnPos.pushAppArg
  let (lhsPos, rhsPos) := if rwLemma.symm then (rhsPos, lhsPos) else (lhsPos, rhsPos)
  .cons rhsPos .wasInserted <|
    .cons lhsPos .wasDeleted .nil

/-- similar to `Name.isBlackListed`. -/
def isBadDecl (name : Name) (cinfo : ConstantInfo) (env : Environment) : Bool :=
  (match cinfo with
    | .axiomInfo v => v.isUnsafe
    | .thmInfo .. => false
    | _ => true)
  || (match name with
    | .str _ "inj"
    | .str _ "injEq"
    | .str _ "sizeOf_spec"
    | .str _ "noConfusionType" => true
    | _ => false)
  || name.isInternalDetail
  || isAuxRecursor env name
  || isNoConfusion env name
  || isMatcherCore env name

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

def updateRefinedDiscrTree (name : Name) (cinfo : ConstantInfo) (d : RefinedDiscrTree RewriteLemma)
    : MetaM (RefinedDiscrTree RewriteLemma) := do
  if isBadDecl name cinfo (← getEnv) then
    return d
  let (vars, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := matchEqn? eqn | return d
  d.insertEqn lhs rhs
    { name, symm := false, numParams := vars.size }
    { name, symm := true,  numParams := vars.size }

section


@[reducible]
def RewriteCache := Std.Tactic.DeclCache (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma)

def RewriteCache.mk (profilingName : String)
  (init : Option (RefinedDiscrTree RewriteLemma) := none) :
    IO RewriteCache :=
  Std.Tactic.DeclCache.mk profilingName pre ({}, {})
    addDecl addLibraryDecl post
where
  pre := do
    let .some libraryTree := init | failure
    return ({}, libraryTree)

  addDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (← updateRefinedDiscrTree name cinfo currentTree, libraryTree)

  addLibraryDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (currentTree, ← updateRefinedDiscrTree name cinfo libraryTree)

  sortLemmas : Array RewriteLemma → Array RewriteLemma :=
    Array.qsort (lt := (· < ·))

  post
    | (currentTree, libraryTree) => do
    return (currentTree.mapArrays sortLemmas, libraryTree.mapArrays sortLemmas)

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `LibraryRewrite.RewriteLemmas).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "LibraryRewrite" / "RewriteLemmas.extra"

initialize cachedData : RewriteCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (RefinedDiscrTree RewriteLemma) path
    -- We can drop the `CompactedRegion` value; we do not plan to free it
    RewriteCache.mk "rewrite lemmas : using cache" (init := some d)
  else
    RewriteCache.mk "rewrite lemmas : init cache"

def getRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma) :=
  cachedData.get

end


/-- The `Expr` at a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.rootExpr : SubExpr.GoalsLocation → MetaM Expr
  | ⟨mvarId, .hyp fvarId⟩        => mvarId.withContext fvarId.getType
  | ⟨mvarId, .hypType fvarId _⟩  => mvarId.withContext fvarId.getType
  | ⟨mvarId, .hypValue fvarId _⟩ => mvarId.withContext do return (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩          => mvarId.getType

/-- The `SubExpr.Pos` of a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.pos : SubExpr.GoalsLocation → SubExpr.Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

/-- find the positions of the pattern that `kabstract` would find -/
def findPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos)
      : MetaM (Array SubExpr.Pos) := do
    let visitChildren : Array SubExpr.Pos → MetaM (Array SubExpr.Pos) :=
      match e with
      | .app f a         => visit f pos.pushAppFn
                        >=> visit a pos.pushAppArg
      | .mdata _ b       => visit b pos
      | .proj _ _ b      => visit b pos.pushProj
      | .letE _ t v b _  => visit t pos.pushLetVarType
                        >=> visit v pos.pushLetValue
                        >=> visit b pos.pushLetBody
      | .lam _ d b _     => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | .forallE _ d b _ => visit d pos.pushBindingDomain
                        >=> visit b pos.pushBindingBody
      | _                => pure
    if e.hasLooseBVars || e.toHeadIndex != pHeadIdx || e.headNumArgs != pNumArgs then
      visitChildren positions
    else
      let mctx ← getMCtx
      if (← isDefEq e p) then
        setMCtx mctx
        visitChildren (positions.push pos)
      else
        visitChildren positions
  visit e .root #[]


open Widget ProofWidgets Jsx

def addDiffs (diffs : AssocList SubExpr.Pos DiffTag)
    (code : CodeWithInfos) : CodeWithInfos :=
  code.map fun info =>
    match diffs.find? info.subexprPos with
      | some diff => { info with diffStatus? := some diff }
      |    none   =>   info

def renderWithDiffs (n : Name) (diffs : AssocList SubExpr.Pos DiffTag) : MetaM Html := do
  let ci ← getConstInfo n
  let e := addDiffs diffs (← Widget.ppExprTagged ci.type)
  return <InteractiveCode fmt={e} />

def rewriteCall (loc : SubExpr.GoalsLocation) (rwLemma : RewriteLemma) : MetaM (Option String) := do
  if loc.loc matches .hypValue .. then return none
  let thm ← mkConstWithFreshMVarLevels rwLemma.name
  let (mvars, _, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := matchEqn? eqn | return none
  let target ← loc.rootExpr
  let subExpr ← Core.viewSubexpr loc.pos target
  let lhs := if rwLemma.symm then rhs else lhs
  unless ← isDefEq lhs subExpr do return none
  -- the part below should ideally be computed lazily.
  let lhs ← instantiateMVars lhs
  let positions ← findPositions lhs target
  let location ← (do match loc.loc with
    | .hyp fvarId
    | .hypType fvarId _ => return s! " at {← fvarId.getUserName}"
    | _ => return "")
  let thm ← instantiateMVars (mkAppN thm mvars)
  let thm := Format.pretty <| ← ppExpr thm
  let symm := if rwLemma.symm then "← " else ""
  let cfg := match positions.findIdx? (· == loc.pos) with
    | none => " /- couldn't find a suitable occurrence -/"
    | some pos =>
      if positions.size == 1 then "" else
      s! " (config := \{ occs := .pos [{pos+1}]})"
  return some s! "rw{cfg} [{symm}{thm}]{location}"

def renderResults (results : Array (Array (RewriteLemma × String))) (isEverything : Bool)
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) : MetaM Html := do
  let htmls ← results.mapM renderBlock
  let htmls := htmls.concatMap (#[·, <hr/>])
  let title := s! "{if isEverything then "All" else "Some"} rewrite suggestions:"
  return <details «open»={true}>
      <summary className="mv2 pointer"> {.text title}</summary>
      {.element "div" #[] htmls}
    </details>
where
  renderBlock (results : Array (RewriteLemma × String)) : MetaM Html := do
    let htmls ← results.mapM fun (rwLemma, call) => do
      let lemmaType ← renderWithDiffs rwLemma.name rwLemma.diffs
      return <li>
          <p> {lemmaType} </p>
          <p> {Html.ofComponent MakeEditLink
            (.ofReplaceRange doc.meta range call none)
            #[.text s! "{rwLemma.name}"]} </p>
        </li>
    return <p> {.element "ul" #[] htmls} </p>

/-- Return all potenital rewrite lemmata -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma × Nat)) := do
  let (localLemmas, libraryLemmas) ← getRewriteLemmas
  let localResults ← localLemmas.getMatchWithScore e (unify := true) (config := {})
  let libraryResults ← libraryLemmas.getMatchWithScore e (unify := true) (config := {})
  let allResults := localResults ++ libraryResults
  return allResults

/-- `Props` for interactive tactics.
    Keeps track of the range in the text document of the piece of syntax to replace. -/
structure InteractiveTacticProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
  factor : Nat
deriving RpcEncodable

@[specialize]
def filterLemmata {α β} (ass : Array (Array α × Nat)) (f : α → MetaM (Option β))
  (maxTotal := 10000) (max := 1000) : MetaM (Array (Array β × Nat) × Bool) :=
  let maxTotal := maxTotal * 1000
  let max := max * 1000
  withCatchingRuntimeEx do
  let startHeartbeats ← IO.getNumHeartbeats
  let mut currHeartbeats := startHeartbeats
  let mut bss := #[]
  let mut isEverything := true
  for (as, n) in ass do
    let mut bs := #[]
    for a in as do
      try
        if let some b ← withTheReader Core.Context ({· with
            initHeartbeats := currHeartbeats
            maxHeartbeats := max }) do
              withoutCatchingRuntimeEx (f a) then
          bs := bs.push b
      catch _ =>
        isEverything := false

      currHeartbeats ← IO.getNumHeartbeats
      if currHeartbeats - startHeartbeats > maxTotal then
        break

    unless bs.isEmpty do
      bss := bss.push (bs, n)
    if currHeartbeats - startHeartbeats > maxTotal then
      return (bss, false)
  return (bss, isEverything)

@[server_rpc_method]
def LibraryRewrite.rpc (props : InteractiveTacticProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back?
    | return <p> rw??: Please shift-click an expression. </p>
  let some goal := props.goals.find? (·.mvarId == loc.mvarId)
    | return <p> Couln't find the goal. </p>
  goal.ctx.val.runMetaM {} do -- similar to `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      let subExpr ← Core.viewSubexpr loc.pos (← loc.rootExpr)
      if subExpr.hasLooseBVars then
        return <p> rw doesn't work with bound variables. </p>
      let rwLemmas ← getCandidates subExpr
      if rwLemmas.isEmpty then
        return <p> No rewrite lemmata found. </p>
      let (results, isEverything) ← filterLemmata rwLemmas (fun rwLemma => OptionT.run do
        return (rwLemma, ← rewriteCall loc rwLemma))
        (max := props.factor * 1000) (maxTotal := props.factor * 10000)
      if results.isEmpty then
        return <p> No applicable rewrite lemmata found. </p>
      renderResults (results.map (·.1)) isEverything props.replaceRange doc

@[widget_module]
def LibraryRewrite : Component InteractiveTacticProps :=
  mk_rpc_widget% LibraryRewrite.rpc

/--
After writing `rw??`, you can shift-click an expression in the fist tactic state goal,
which makes a list of rewrite suggestions appear for rewriting the selected expression.
Clicking on the lemma name of a suggestion will paste the rewrite tactic into the editor.

`rw??` is limited to run for a short amount of time, but if you want it to run for longer,
you can specify a factor by which to increase the available heartbeats.
If all possible results have been listed, it says `All rewrite results:`.
-/
syntax (name := rw??) "rw??" (num)? : tactic

@[tactic Mathlib.Tactic.LibraryRewrite.rw??]
def elabRw?? : Elab.Tactic.Tactic := fun stx => match stx with
  | `(tactic| rw?? $(factor)?) => do
    let some range := (← getFileMap).rangeOfStx? stx | return
    let factor := match factor with | some n => n.raw.isNatLit?.getD 1 | none => 1
    Widget.savePanelWidgetInfo (hash LibraryRewrite.javascript)
      (pure $ json% { replaceRange : $(range), factor : $(factor) }) stx
  | _ => Elab.throwUnsupportedSyntax
