/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.RefinedDiscrTree
import Mathlib.Tactic.Widget.SelectPanelUtils
namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta Server

/-- The structure that is stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  name : Name
  symm : Bool
  numParams : Nat
deriving BEq, Inhabited

/-- Return the string length of the lemma name. -/
def RewriteLemma.length (rwLemma : RewriteLemma) : Nat :=
  rwLemma.name.toString.length

/--
We sort lemmata by the following conditions (in order):
- number of parameters
- left-to-right rewrites come first
- length of the name
- alphabetical order
-/
def RewriteLemma.lt (a b : RewriteLemma) : Bool :=
  a.numParams < b.numParams || a.numParams == b.numParams &&
    (!a.symm && b.symm || a.symm == b.symm &&
      (a.length < b.length || a.length == b.length &&
        Name.lt a.name b.name))

instance : LT RewriteLemma := ⟨fun a b => RewriteLemma.lt a b⟩
instance (a b : RewriteLemma) : Decidable (a < b) :=
  inferInstanceAs (Decidable (RewriteLemma.lt a b))

/-- Similar to `Name.isBlackListed`. -/
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
  || (`Mathlib).isPrefixOf name
  || isAuxRecursor env name
  || isNoConfusion env name
  || isMatcherCore env name

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def updateDiscrTree (name : Name) (cinfo : ConstantInfo) (d : RefinedDiscrTree RewriteLemma) :
    MetaM (RefinedDiscrTree RewriteLemma) := do
  if isBadDecl name cinfo (← getEnv) then
    return d
  let (vars, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := matchEqn? eqn | return d
  d.insertEqn lhs rhs
    { name, symm := false, numParams := vars.size }
    { name, symm := true,  numParams := vars.size }

section

open Std.Tactic

@[reducible]
def RewriteCache := DeclCache (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma)

def RewriteCache.mk
  (init : Option (RefinedDiscrTree RewriteLemma) := none) :
    IO RewriteCache :=
  DeclCache.mk "rw??: init cache" pre ({}, {}) addDecl addLibraryDecl post
where
  pre := do
    let .some libraryTree := init | failure
    return ({}, libraryTree)

  addDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (← updateDiscrTree name cinfo currentTree, libraryTree)

  addLibraryDecl (name : Name) (cinfo : ConstantInfo)
    | (currentTree, libraryTree) => do
    return (currentTree, ← updateDiscrTree name cinfo libraryTree)

  post
    | (currentTree, libraryTree) => do
    return (currentTree, libraryTree.mapArrays (·.qsort (· < ·)))

def cachePath : IO System.FilePath := do
  try
    return (← findOLean `MathlibExtras.LibraryRewrites).withExtension "extra"
  catch _ =>
    return ".lake" / "build" / "lib" / "MathlibExtras" / "LibraryRewrites.extra"

initialize cachedData : RewriteCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (RefinedDiscrTree RewriteLemma) path
    -- We can drop the `CompactedRegion` value; we do not plan to free it
    RewriteCache.mk (init := some d)
  else
    RewriteCache.mk

def getRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma × RefinedDiscrTree RewriteLemma) := do
  let (currentTree, libraryTree) ← cachedData.get
  return (currentTree.mapArrays (·.qsort (· < ·)), libraryTree)

end


/-- The `Expr` at a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.rootExpr : SubExpr.GoalsLocation → MetaM Expr
  | ⟨_, .hyp fvarId⟩        => fvarId.getType
  | ⟨_, .hypType fvarId _⟩  => fvarId.getType
  | ⟨_, .hypValue fvarId _⟩ => do return (← fvarId.getDecl).value
  | ⟨mvarId, .target _⟩     => mvarId.getType

/-- The `SubExpr.Pos` of a `SubExpr.GoalsLocation`. -/
def _root_.Lean.SubExpr.GoalsLocation.pos : SubExpr.GoalsLocation → SubExpr.Pos
  | ⟨_, .hyp _⟩          => .root
  | ⟨_, .hypType _ pos⟩  => pos
  | ⟨_, .hypValue _ pos⟩ => pos
  | ⟨_, .target pos⟩     => pos

/-- find the positions of the pattern that `kabstract` would find -/
def kabstractPositions (p e : Expr) : MetaM (Array SubExpr.Pos) := do
  let e ← instantiateMVars e
  let pHeadIdx := p.toHeadIndex
  let pNumArgs := p.headNumArgs
  let rec visit (e : Expr) (pos : SubExpr.Pos) (positions : Array SubExpr.Pos) :
      MetaM (Array SubExpr.Pos) := do
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

def RewriteLemma.pattern (rwLemma : RewriteLemma) : MetaM CodeWithInfos := do
  let cinfo ← getConstInfo rwLemma.name
  forallTelescope cinfo.type fun _ e => do
    let some (lhs, rhs) := matchEqn? e | throwError "Expected equation, not {indentExpr e}"
    let side := if rwLemma.symm then rhs else lhs
    ppExprTagged side

open PrettyPrinter Delaborator SubExpr in
/-- if `e` is an application of a rewrite lemma,
return `e` as a string for pasting into the editor.

if `explicit = true`, we print the lemma application explicitly. This is for when the rewrite
creates new goals.
We avoid printing instance arguments or universe levels by setting their options to `false`.
We ignore any `Options` set by the user. -/
def printRewriteLemma (e : Expr) (explicit : Bool) : MetaM String :=
  withOptions (fun _ => Options.empty
    |>.setBool `pp.universes false
    |>.setBool `pp.instances false
    |>.setBool `pp.unicode.fun true) do
  if explicit then
    let (stx, _) ← delabCore e (delab := delabExplicit)
    return Format.pretty (← ppTerm stx)
  else
    return Format.pretty (← Meta.ppExpr e)
where
  /-- See `delabApp` and `delabAppCore`. -/
  delabExplicit : Delab := do
    let e ← getExpr
    let paramKinds ← getParamKinds e.getAppFn e.getAppArgs
    delabAppExplicitCore e.getAppNumArgs delabConst paramKinds

structure RewriteApplication extends RewriteLemma where
  tactic : String
  replacement : CodeWithInfos
  replacementS : String := replacement.stripTags
  extraGoals : Array CodeWithInfos

def rewriteCall (rwLemma : RewriteLemma)
    (loc : SubExpr.GoalLocation) (subExpr : Expr) (occ : Option Nat) :
    MetaM (Option RewriteApplication) := do
  let thm ← mkConstWithFreshMVarLevels rwLemma.name
  let (mvars, bis, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := matchEqn? eqn | return none
  let (lhs, rhs) := if rwLemma.symm then (rhs, lhs) else (lhs, rhs)
  unless ← withReducible (isDefEq lhs subExpr) do return none

  let mut extraGoals := #[]
  let mut allAssigned := true
  for mvar in mvars, bi in bis do
    let mvarId := mvar.mvarId!
    -- we need to check that all instances can be synthesized
    if bi.isInstImplicit then
      let .some _  ← trySynthInstance (← mvarId.getType) | return none
      -- maybe check that the synthesized instance and `mvar` are `isDefEq`
    else if !(← mvarId.isAssigned) then
      allAssigned := false
      -- if the userName has macro scopes, we can't use the name, so we use `?_` instead
      if (← mvarId.getDecl).userName.hasMacroScopes then
        mvarId.setUserName `«_»
      if bi.isExplicit then
        let extraGoal ← instantiateMVars (← mvarId.getType)
        extraGoals := extraGoals.push (← ppExprTagged extraGoal)

  let replacement ← ppExprTagged (← instantiateMVars rhs)
  let lemmaApplication ← instantiateMVars (mkAppN thm mvars)

  let location ← (do match loc with
    | .hyp fvarId
    | .hypType fvarId _ => return s! " at {← fvarId.getUserName}"
    | _ => return "")
  let symm := if rwLemma.symm then "← " else ""
  let cfg := match occ with
    | none => ""
    | some occ => s! " (config := \{ occs := .pos [{occ}]})"
  let tactic := s! "rw{cfg} [{symm}{← printRewriteLemma lemmaApplication !allAssigned}]{location}"
  return some { rwLemma with tactic, extraGoals, replacement }


def renderResults (results : Array (CodeWithInfos × Array RewriteApplication))
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) : Html :=
  let htmls := results.map (fun (t, arr) => renderBlock t arr);
  <details «open»={true}>
    <summary className="mv2 pointer"> Rewrite suggestions: </summary>
    {.element "div" #[("style", json% {"marginLeft" : "4px"})] htmls}
  </details>
where
  renderBlock (title : CodeWithInfos) (results : Array RewriteApplication) : Html :=
    let core :=
      .element "ul" #[] <|
      results.map fun rw =>
        let button := Html.ofComponent MakeEditLink
              (.ofReplaceRange doc.meta range rw.tactic none)
              #[.text rw.replacementS]
        let extraGoals := rw.extraGoals.concatMap fun extraGoal => #[
          <br/>,
          <strong className="goal-vdash">⊢ </strong>,
          <InteractiveCode fmt={extraGoal}/>];
        <li>
          {.element "p" #[] (#[button] ++ extraGoals)}
        </li>;
    <details «open»={true}>
      <summary className="mv2 pointer">
        {.text "Pattern "} <InteractiveCode fmt={title}/>
      </summary>
      {core}
    </details>

/-- Return all potenital rewrite lemmata -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma × Nat)) := do
  let (localLemmas, libraryLemmas) ← getRewriteLemmas
  let localResults ← localLemmas.getMatchWithScore e (unify := true)
  let libraryResults ← libraryLemmas.getMatchWithScore e (unify := true)
  let allResults := localResults ++ libraryResults
  return allResults

def checkLemmata (ass : Array (Array RewriteLemma × Nat))
    (loc : SubExpr.GoalLocation) (subExpr : Expr) (occ : Option Nat) :
    MetaM (Array (CodeWithInfos × Array RewriteApplication)) := do
  let mut bss := #[]
  for (as, _n) in ass do
    let mut bs := #[]
    for a in as do
      if let some b ← rewriteCall a loc subExpr occ then
        bs := bs.push b

    if h : bs.size ≥ 1 then do
      let pattern ← bs[0].pattern
      bss := bss.push (pattern, bs)
  return bss

/-- Remove duplicate lemmata and lemmata that do not change the expression. -/
def dedupLemmata (lemmata : Array RewriteApplication) (subExprString : String) :
    Array RewriteApplication :=
  let replacements : HashMap String Name := lemmata.foldl (init := .empty) fun map lem =>
    if lem.extraGoals.isEmpty && !map.contains lem.replacementS then
      map.insert lem.replacementS lem.name
    else
      map
  lemmata.filter fun lem =>
    if lem.replacementS == subExprString then
      false
    else
      match replacements.find? lem.replacementS with
      | some name => name == lem.name
      | none      => true

def getLibraryRewrites (loc : SubExpr.GoalsLocation) :
    ExceptT String MetaM (Array (CodeWithInfos × Array RewriteApplication)) := do
  let e ← loc.rootExpr
  let pos := loc.pos
  let loc := loc.loc
  let subExpr ← Core.viewSubexpr pos e
  if subExpr.hasLooseBVars then
    throwThe _ "rw doesn't work on expressions with bound variables."
  let rwLemmas ← getCandidates subExpr
  if rwLemmas.isEmpty then
    throwThe _ "No rewrite lemmata found."
  let positions ← kabstractPositions subExpr e
  let occurrence := if positions.size == 1 then none else
    positions.findIdx? (· == pos) |>.map (· + 1)
  let results ← checkLemmata rwLemmas loc subExpr occurrence
  if results.isEmpty then
    throwThe _ "No applicable rewrite lemmata found."
  let subExprString := (← ppExprTagged subExpr).stripTags
  return results.map fun (pat, lemmata) => (pat, dedupLemmata lemmata subExprString)

@[server_rpc_method]
def LibraryRewrite.rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
  RequestM.asTask do
  let doc ← RequestM.readDoc
  let some loc := props.selectedLocations.back? |
    return .text "rw??: Please shift-click an expression."
  if loc.loc matches .hypValue .. then
    return .text "rw doesn't work on the value of a let-bound free variable."
  let some goal := props.goals[0]? |
    return .text "There is no goal to solve!"
  if loc.mvarId != goal.mvarId then
    return .text "The selected expression should be in the main goal."
  goal.ctx.val.runMetaM {} do -- similar to `SelectInsertConv`
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      profileitM Exception "libraryRewrite" (← getOptions) do
        (fun
          | .ok results => renderResults results props.replaceRange doc
          | .error msg  => .text msg)
        <$> getLibraryRewrites loc

@[widget_module]
def LibraryRewrite : Component SelectInsertParams :=
  mk_rpc_widget% LibraryRewrite.rpc

/--
After writing `rw??`, shift-click an expression in the tactic state.
This creates a list of rewrite suggestions for the selected expression.
Clicking on a suggestion will paste the `rw` tactic into the editor.
-/
syntax (name := rw??) "rw??" : tactic

@[tactic Mathlib.Tactic.LibraryRewrite.rw??]
def elabRw?? : Elab.Tactic.Tactic := fun stx => match stx with
  | `(tactic| rw??) => do
    let some range := (← getFileMap).rangeOfStx? stx | return
    Widget.savePanelWidgetInfo (hash LibraryRewrite.javascript)
      (pure $ json% { replaceRange : $(range) }) stx
  | _ => Elab.throwUnsupportedSyntax
