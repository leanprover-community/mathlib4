/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Tactic.InteractiveUnfold
import Std.Util.Cache
import Std.Util.Pickle

/-!
# Point & click library rewriting

This file defines `rw??`, an interactive tactic that suggests rewrites for any expression selected
by the user.

We use a cached `RefinedDiscrTree` to lookup a list of candidate rewrite lemmas. The cache
excludes lemmas defined in the `Mathlib/Tactic` folder, since these lemmas aren't
supposed to ever be used directly.

After this, each lemma is checked one by one to see whether it is applicable.

The `RefinedDiscrTree` lookup groups the results by match pattern and gives a score to each pattern.
This is used to display the results in sections, ordered by the score of the pattern.

When a rewrite lemma intoduces new goals, these are shown with a `⊢`.

The filter icon can be used to switch to an unfiltered view that also gives the lemma names.
-/

namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta Server

/-- The rewrite lemma structure that we store in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The name of the lemma -/
  name : Name
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- The number of arguments that the lemma takes -/
  numParams : Nat
deriving BEq, Inhabited

/-- The string length of the lemma name. -/
def RewriteLemma.length (rwLemma : RewriteLemma) : Nat :=
  rwLemma.name.toString.length

/--
We sort lemmas by the following conditions (in order):
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

/-- Return whether the definitions in this module should be ignored. -/
def isBadModule (name : Name) : Bool :=
  (`Mathlib.Tactic).isPrefixOf name

/-- Similar to `Name.isBlackListed`. -/
def isBadDecl (name : Name) (cinfo : ConstantInfo) (env : Environment) : Bool :=
  (match cinfo with
    | .thmInfo .. => false
    | .axiomInfo v => v.isUnsafe
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
  -- don't index lemmas of the form `a = ?b` where `?b` is a variable not appearing in `a`?
  if let .mvar mvarId := lhs then
    if (rhs.findMVar? (· == mvarId)).isNone then
      return d
  if let .mvar mvarId := rhs then
    if (lhs.findMVar? (· == mvarId)).isNone then
      return d
  d.insertEqn lhs rhs
    { name, symm := false, numParams := vars.size }
    { name, symm := true,  numParams := vars.size }

section Cache

open Std.Tactic

@[reducible]
private def RewriteCache := Cache (RefinedDiscrTree RewriteLemma)

/-- Construct the `RewriteCache` of all lemmas. -/
def RewriteCache.mk : IO RewriteCache :=
  Cache.mk do
    profileitM Exception "rw??: init cache" (← getOptions) do
      let env ← getEnv
      let mut tree := {}
      for moduleName in env.header.moduleNames, data in env.header.moduleData do
        if isBadModule moduleName then
          continue
        for cinfo in data.constants do
          tree ← updateDiscrTree cinfo.name cinfo tree
      return tree.mapArrays (·.qsort (· < ·))

/-- The file path of the pre-build `RewriteCache` cache -/
def cachePath : IO System.FilePath := do
  try
    return (← findOLean `MathlibExtras.LibraryRewrites).withExtension "extra"
  catch _ =>
    return ".lake" / "build" / "lib" / "MathlibExtras" / "LibraryRewrites.extra"

private initialize cachedData : RewriteCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (RefinedDiscrTree RewriteLemma) path
    Cache.mk (pure d)
  else
    RewriteCache.mk

/-- Get the `RefinedDiscrTree` of all rewrite lemmas, attempting to get it from pre-built cache. -/
def getCachedRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma) :=
  cachedData.get

/-- Construct the `RefinedDiscrTree` of all lemmas defined in the current file. -/
def getLocalRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma) := do
  (← getEnv).constants.map₂.foldlM (init := {}) (fun tree n c => updateDiscrTree n c tree)

end Cache



/-- Return all potential rewrite lemmas -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma × Bool)) := do
  let localResults  ← (← getLocalRewriteLemmas ).getMatchWithScore e (unify := false)
  let cachedResults ← (← getCachedRewriteLemmas).getMatchWithScore e (unify := false)
  let allResults := localResults.map (·.1, true) ++ cachedResults.map (·.1, false)
  return allResults

/-- A rewrite lemma that has been applied to an expression. -/
structure Rewrite extends RewriteLemma where
  /-- The proof of the rewrite -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The extra goals created by the rewrite -/
  extraGoals : Array (MVarId × BinderInfo)

/-- If `rwLemma` can be used to rewrite `e`, return the rewrite. -/
def checkLemma (rwLemma : RewriteLemma) (e : Expr) : MetaM (Option Rewrite) := do
  let thm ← mkConstWithFreshMVarLevels rwLemma.name
  let (mvars, binderInfos, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := matchEqn? eqn | return none
  let (lhs, rhs) := if rwLemma.symm then (rhs, lhs) else (lhs, rhs)
  unless ← withReducible (isDefEq lhs e) do return none

  let mut extraGoals := #[]
  for mvar in mvars, bi in binderInfos do
    -- we need to check that all instances can be synthesized
    if bi.isInstImplicit then
      let .some inst ← trySynthInstance (← mvar.mvarId!.getType) | return none
      unless ← isDefEq inst mvar do
        return none
    else
      unless ← mvar.mvarId!.isAssigned do
        extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let proof ← instantiateMVars (mkAppN thm mvars)
  return some { rwLemma with proof, replacement, extraGoals }

/-- Return all applicable library rewrites of `e`.
The `Bool` indicates whether the lemmas are from the current file. -/
def getRewrites (e : Expr) : MetaM (Array (Array Rewrite × Bool)) := do
  let candidates ← getCandidates e
  candidates.filterMapM fun (candidates, isLocal) => do
    let rewrites ← candidates.filterMapM fun cand =>
      withCatchingRuntimeEx do
      try withoutCatchingRuntimeEx <|
        checkLemma cand e
      catch _ =>
        return none
    if rewrites.isEmpty then
      return none
    return (rewrites, isLocal)

/-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
def getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType matches .forallE .. do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ _ b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    result := result.push bi
  return result

/-- Determine whether the explicit parts of two expressions are equal,
and the implicit parts are definitionally equal. -/
partial def isExplicitEq (t s : Expr) : MetaM Bool := do
  if t == s then
    return true
  unless t.getAppNumArgs == s.getAppNumArgs && t.getAppFn == s.getAppFn do
    return false
  let tArgs := t.getAppArgs
  let sArgs := s.getAppArgs
  let bis ← getBinderInfos t.getAppFn tArgs
  t.getAppNumArgs.allM fun i =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
      isDefEq tArgs[i]! sArgs[i]!

/-- Filter out duplicate rewrites or reflexive rewrites. -/
def filterRewrites {α} (e : Expr) (rewrites : Array α) (replacement : α → Expr) :
    MetaM (Array α) :=
  withNewMCtxDepth do
  let mut filtered := #[]
  for rw in rewrites do
    unless (← isExplicitEq (replacement rw) e <||>
        filtered.anyM (isExplicitEq (replacement rw) $ replacement ·)) do
      filtered := filtered.push rw
  return filtered


/-! ### User interface code -/

open PrettyPrinter Delaborator SubExpr in
/-- if `e` is an application of a rewrite lemma,
return `e` as a string for pasting into the editor.

if `explicit = true`, we print the lemma application explicitly. This is for when the rewrite
creates new goals.
We ignore `Options` set by the user. -/
def printRewriteLemma (e : Expr) (explicit : Bool) : MetaM String :=
  if explicit then
    withOptions (fun _ => Options.empty
      |>.setBool `pp.universes false
      |>.setBool `pp.match false
      |>.setBool `pp.instances false
      |>.setBool `pp.unicode.fun true) do
    let (stx, _) ← delabCore e (delab := delabExplicit)
    return Format.pretty (← ppTerm stx) (width := 90) (indent := 2)
  else
    PasteString e
where
  /-- See `delabApp` and `delabAppCore`. -/
  delabExplicit : Delab := do
    let e ← getExpr
    let paramKinds ← getParamKinds e.getAppFn e.getAppArgs
    delabAppExplicitCore e.getAppNumArgs delabConst paramKinds

/-- Return a unique name for a metavariable based on the given suggestion.
Similar to `Lean.Meta.getUnusedUserName`, which is for free variables. -/
partial def getUnusedMVarName (suggestion : Name) (names : PersistentHashMap Name MVarId)
    (i : Option Nat := none) : Name :=
  let name := match i with
    | some i => match suggestion with
      | .str p s => .str p s! "{s}_{i}"
      | n => .str n s! "_{i}"
    | none => suggestion
  if names.contains name then
    let i' : Nat := match i with
      | some i => i+1
      | none => 1
    getUnusedMVarName suggestion names i'
  else
    name

/-- Return the rewrite tactic that performs the rewrite. -/
def tacticString (rw : Rewrite) (occ : Option Nat) (loc : Option Name)
    (initNames : PersistentHashMap Name MVarId) : MetaM String := do
  let mut initNames := initNames
  for (mvarId, _) in rw.extraGoals do
    unless ← mvarId.isAssigned do
      let name ← mvarId.getTag
      -- if the userName has macro scopes, it comes from a non-dependent arrow,
      -- so we use `?_` instead
      if name.hasMacroScopes then
        mvarId.setTag `«_»
      else
        let name := getUnusedMVarName name initNames
        mvarId.setTag name
        initNames := initNames.insert name mvarId
  let proof ← printRewriteLemma rw.proof !rw.extraGoals.isEmpty
  return mkRewrite occ rw.symm proof loc

open Widget ProofWidgets Jsx

/-- The structure with all data necessary for rendering a rewrite suggestion -/
structure RewriteInterface extends RewriteLemma where
  /-- The rewrite tactic string that performs the rewrite -/
  tactic : String
  /-- The replacement expression obtained from the rewrite -/
  replacementExpr : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : String
  /-- The extra goals created by the rewrite -/
  extraGoals : Array CodeWithInfos
  /-- The lemma name with hover information -/
  prettyLemma : CodeWithInfos

/-- Construct the `RewriteInterface` from a `Rewrite`. -/
def Rewrite.toInterface (rw : Rewrite) (occ : Option Nat) (loc : Option Name)
    (initNames : PersistentHashMap Name MVarId) : MetaM RewriteInterface := do
  let tactic ← tacticString rw occ loc initNames
  let replacement := Format.pretty (← ppExpr rw.replacement)
  let mut extraGoals := #[]
  for (mvarId, bi) in rw.extraGoals do
    if bi.isExplicit then
      let extraGoal ← ppExprTagged (← instantiateMVars (← mvarId.getType))
      extraGoals := extraGoals.push extraGoal
  let prettyLemma : CodeWithInfos := match ← ppExprTagged (← mkConstWithLevelParams rw.name) with
    | .tag tag _ => .tag tag (.text s!"{rw.name}")
    | code => code
  return { rw with tactic, replacement, extraGoals, prettyLemma, replacementExpr := rw.replacement }

/-- Return the Interfaces for rewriting `e`, both filtered and unfiltered. -/
def getRewriteInterfaces (e : Expr) (occ : Option Nat) (loc : Option Name)
    (initNames : PersistentHashMap Name MVarId) :
    MetaM (Array (Array RewriteInterface × Bool) × Array (Array RewriteInterface × Bool)) := do
  let mut dedup := #[]
  let mut all := #[]
  for (rewrites, isLocal) in ← getRewrites e do
    let rewrites ← rewrites.mapM (·.toInterface occ loc initNames)
    let filtered ← filterRewrites e rewrites (·.replacementExpr)
    all := all.push (rewrites, isLocal)
    unless filtered.isEmpty do
      dedup := dedup.push (filtered, isLocal)
  return (dedup, all)

/-- Render the matching side of the rewrite lemma.
This is shown at the header of each section of rewrite results. -/
def RewriteLemma.pattern {α} (rwLemma : RewriteLemma) (k : Expr → MetaM α) : MetaM α := do
  let cinfo ← getConstInfo rwLemma.name
  forallTelescope cinfo.type fun _ e => do
    let some (lhs, rhs) := matchEqn? e | throwError "Expected equation, not {indentExpr e}"
    let side := if rwLemma.symm then rhs else lhs
    k side

/-- Render the given rewrite results. -/
def renderRewrites (results : Array (Array RewriteInterface × Bool)) (init : Option Html)
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) (showNames : Bool) : MetaM Html := do
  let htmls ← results.filterMapM (renderSection showNames)
  let htmls := match init with
      | some html => #[html] ++ htmls
      | none => htmls
  if htmls.isEmpty then
    return .text "No rewrites found."
  else
    return .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls
where
  /-- Render one section of rewrite results. -/
  renderSection (showNames : Bool) (sec : Array RewriteInterface × Bool) : MetaM (Option Html) := do
    let some head := sec.1[0]? | return none
    return <details «open»={true}>
      <summary className="mv2 pointer">
        Pattern
        {← head.pattern (return <InteractiveCode fmt={← ppExprTagged ·}/>)}
        {.text (if sec.2 then "(local results)" else "")}
      </summary>
      {renderSectionCore showNames sec.1}
    </details>

  /-- Render the list of rewrite results in one section. -/
  renderSectionCore (showNames : Bool) (sec : Array RewriteInterface) : Html :=
    .element "ul" #[("style", json% { "padding-left" : "30px"})] <|
    sec.map fun rw =>
      <li> { .element "p" #[] <|
        let button :=
          <span className="font-code"> {
            Html.ofComponent MakeEditLink
              (.ofReplaceRange doc.meta range rw.tactic)
              #[.text rw.replacement] }
          </span>
        let extraGoals := rw.extraGoals.concatMap fun extraGoal =>
          #[<br/>, <strong className="goal-vdash">⊢ </strong>, <InteractiveCode fmt={extraGoal}/>]
        #[button] ++ extraGoals ++
          if showNames then #[<br/>, <InteractiveCode fmt={rw.prettyLemma}/>] else #[] }
      </li>

/-- The props for the `FilterDetails` component. -/
structure FilterDetailsProps where
  /-- The title -/
  message : String
  /-- What is shown in the filtered state -/
  filtered : Html
  /-- What is shown in the non-filtered state -/
  all : Html
  /-- Whether to start in the filtered state -/
  initiallyFiltered : Bool
deriving RpcEncodable

/-- `FilterDetails` is a details component that has a button for switching between a filtered
and a non-filtered view. -/
@[widget_module]
def FilterDetails : Component FilterDetailsProps where
  javascript := include_str "LibraryRewrite" / "FilterDetails.js"

@[server_rpc_method_cancellable]
private def rpc (props : SelectInsertParams) : RequestM (RequestTask Html) :=
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
  goal.ctx.val.runMetaM {} do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      profileitM Exception "rw??" (← getOptions) do

        let { userNames := initNames, .. } ← getMCtx
        let some (subExpr, occ) ← viewKAbstractSubExpr (← loc.rootExpr) loc.pos |
          return .text "rw doesn't work on expressions with bound variables."
        let location ← loc.location

        let unfoldsHtml ←
          InteractiveUnfold.renderDefinitions subExpr occ location props.replaceRange doc

        let (filtered, all) ← getRewriteInterfaces subExpr occ location initNames
        let filtered ← renderRewrites filtered unfoldsHtml props.replaceRange doc false
        let all      ← renderRewrites all      unfoldsHtml props.replaceRange doc true
        return <FilterDetails
          message={"Rewrite suggestions:"}
          all={all}
          filtered={filtered}
          initiallyFiltered={true} />

/-- The component called by the `rw??` tactic -/
@[widget_module]
def LibraryRewriteComponent : Component SelectInsertParams :=
  mk_rpc_widget% LibraryRewrite.rpc

/--
To use `rw??`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `rw??` by a tactic that performs this rewrite.
Click on the filter icon to switch to an unfiltered view that also shows the lemma names.
-/
elab stx:"rw??" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash LibraryRewriteComponent.javascript)
    (pure $ json% { replaceRange : $range }) stx

/-- Represent a `Rewrite` as `MessageData`. -/
private def Rewrite.toMessageData (rw : Rewrite) : MetaM MessageData := do
  let extraGoals ← rw.extraGoals.filterMapM fun (mvarId, bi) => do
    if bi.isExplicit then
      return some m! "⊢ {← mvarId.getType}"
    return none
  let list := [m! "{rw.replacement}"]
      ++ extraGoals.toList
      ++ [m! "{rw.name}"]
  return .group <| .nest 2 <| "· " ++ .joinSep list "\n"

/-- Represent a section of rewrites as `MessageData`. -/
private def SectionToMessageData (sec : Array Rewrite × Bool) : MetaM (Option MessageData) := do
  let rewrites ← sec.1.toList.mapM (·.toMessageData)
  let rewrites : MessageData := .group (.joinSep rewrites "\n")
  let some head := sec.1[0]? | return ""
  let head ← head.pattern (do
    let ctx : MessageDataContext :=
      { env := ← getEnv, mctx := ← getMCtx, lctx := ← getLCtx, opts := ← getOptions }
    return .withContext ctx m! "{·}")
  return some $ "Pattern " ++ head ++ "\n" ++ rewrites

/-- `#rw?? e` gives all possible rewrites of `e`.
In tactic mode, use `rw??` instead. -/
syntax (name := rw??Command) "#rw??" term : command

open Elab
/-- Elaborate a `#rw??` command. -/
@[command_elab rw??Command]
def elabrw??Command : Command.CommandElab := fun stx =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => do
    let e ← Term.elabTerm stx[1] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Term.levelMVarToParam (← instantiateMVars e)
    let rewrites ← getRewrites e
    let rewrites ← rewrites.mapM fun (rewrites, isLocal) =>
      return (← filterRewrites e rewrites (·.replacement), isLocal)
    let sections ← liftMetaM $ rewrites.filterMapM SectionToMessageData
    logInfo (.joinSep (sections.toList) "\n\n")
