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
excludes lemmas defined in `Mathlib/Tactic/**` and `Init/Omega/**`, since these lemmas aren't
supposed to ever be used directly.

After this, each lemma is checked one by one to see whether it is applicable.

The `RefinedDiscrTree` lookup groups the results by match pattern and gives a score to each pattern.
This is used to display the results in sections. The sections are ordered by this score.
Within each section, the lemmas are sorted by
- number of extra goals
- left-to-right rewrites come first
- length of the lemma name
- alphabetical order of the lemma name

The lemmas are optionally filtered to avoid duplicate rewrites, or trivial rewrites. This
is controlled by the filter button on the top right of the results.

When a rewrite lemma introduces new goals, these are shown after a `⊢`.

-/

/-! ### Caching -/

namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta Server

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The name of the lemma -/
  name : Name
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
deriving BEq, Inhabited

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
def updateDiscrTree {α} [BEq α] (tree : RefinedDiscrTree α) (l r : α) (type : Expr) :
    MetaM (RefinedDiscrTree α) := do
  let (_, _, eqn) ← forallMetaTelescope type
  let some (lhs, rhs) := matchEqn? eqn | return tree
  -- don't index lemmas of the form `a = ?b` where `?b` is a variable not appearing in `a`
  if let .mvar mvarId := lhs then
    if (rhs.findMVar? (· == mvarId)).isNone then
      return tree
  if let .mvar mvarId := rhs then
    if (lhs.findMVar? (· == mvarId)).isNone then
      return tree
  tree.insertEqn lhs rhs l r

/-- The type of the library rewrite cache. -/
abbrev RewriteCache := Std.Tactic.Cache (RefinedDiscrTree RewriteLemma)

/-- Construct the `RewriteCache` of all lemmas. -/
def RewriteCache.mk : IO RewriteCache :=
  Std.Tactic.Cache.mk do
    profileitM Exception "rw??: init cache" (← getOptions) do
      let env ← getEnv
      env.constants.map₁.foldM (init := {}) fun tree name cinfo =>
        if isBadDecl name cinfo env then pure tree else updateDiscrTree tree
          ⟨name, false⟩ ⟨name, true⟩ cinfo.type


/-- The file path of the pre-build `RewriteCache` cache -/
def cachePath : IO System.FilePath := do
  try
    return (← findOLean `MathlibExtras.LibraryRewrite).withExtension "extra"
  catch _ =>
    return ".lake" / "build" / "lib" / "MathlibExtras" / "LibraryRewrite.extra"

private initialize cachedData : RewriteCache ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, _r) ← unpickle (RefinedDiscrTree RewriteLemma) path
    Std.Tactic.Cache.mk (pure d)
  else
    RewriteCache.mk

/-- Get the `RefinedDiscrTree` of all rewrite lemmas, attempting to get it from pre-built cache. -/
def getCachedRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma) :=
  cachedData.get

/-! ### Computing the Rewrites -/

/-- An option allowing the user to control which modules will not be considered in library search -/
register_option librarySearch.excludedModules : String := {
  defValue := "Init.Omega Mathlib.Tactic"
  descr :=
    "list of modules that should not be considered in library search (separated by white space)"
}

/-- Get the names of the modules that should not be considered in library search. -/
def getLibrarySearchExcludedModules (o : Options) : List Name :=
  (librarySearch.excludedModules.get o).splitOn.filterMap (match ·.toName with
    | .anonymous => none
    | name => name)

/-- Determine whether the list of names contains a prefix of the name. -/
def containsPrefixOf (names : List Name) (name : Name) : Bool :=
  names.any (·.isPrefixOf name)

/-- Get all potential rewrite lemmas from the dicrimination tree. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let cachedResults ← (← getCachedRewriteLemmas).getMatch e (unify := false)
  let excludedModules := getLibrarySearchExcludedModules (← getOptions)
  let env ← getEnv
  return cachedResults.map <|
    Array.filterMap fun rw =>
      env.const2ModIdx.find? rw.name >>= fun idx =>
      if containsPrefixOf excludedModules env.header.moduleNames[idx.toNat]!
      then none else some rw

/-- A rewrite lemma that has been applied to an expression. -/
structure Rewrite where
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- The proof of the rewrite -/
  proof : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The extra goals created by the rewrite -/
  extraGoals : Array (MVarId × BinderInfo)

/-- If `thm` can be used to rewrite `e`, return the rewrite. -/
def checkRewrite (thm e : Expr) (symm : Bool) : MetaM (Option Rewrite) := do
  withTraceNodeBefore `rw?? (return m!
    "rewriting {e} by {if symm then "← " else ""}{thm}") do
  let (mvars, binderInfos, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := matchEqn? eqn | return none
  let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments before unifying
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    return none
  let unifies ← withTraceNodeBefore `rw?? (return m! "unifying {e} =?= {lhs}")
    (withReducible (isDefEq lhs e))
  unless unifies do
    return none
  let mut extraGoals := #[]
  for mvar in mvars, bi in binderInfos do
    -- we need to check that all instances can be synthesized
    if bi.isInstImplicit then
      let some inst ← withTraceNodeBefore `rw?? (return m! "synthesising {← mvar.mvarId!.getType}")
        (synthInstance? (← mvar.mvarId!.getType)) | return none
      let unifies ← withTraceNodeBefore `rw??
        (return m! "unifying with synthesized instance {mvar} =?= {inst}")
        (isDefEq inst mvar)
      unless unifies do
        return none
    else
      unless ← mvar.mvarId!.isAssigned do
        extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let proof ← instantiateMVars (mkAppN thm mvars)
  return some { symm, proof, replacement, extraGoals }

initialize
  registerTraceClass `rw??

/-- Try to rewrite `e` with each of the rewrite lemmas, and sort the resulting rewrites. -/
def checkAndSortRewriteLemmas (e : Expr) (rewrites : Array RewriteLemma) :
    MetaM (Array (Rewrite × Name)) := do
  let rewrites ← rewrites.filterMapM fun rw =>
    withCatchingRuntimeEx do
    try withoutCatchingRuntimeEx do
      let thm ← mkConstWithFreshMVarLevels rw.name
      OptionT.run do (·, rw.name) <$> checkRewrite thm e rw.symm
    catch _ =>
      return none
  let lt (a b : (Rewrite × Name)) :=
    a.1.extraGoals.size < b.1.extraGoals.size || a.1.extraGoals.size == b.1.extraGoals.size &&
      (!a.1.symm && b.1.symm || a.1.symm == b.1.symm &&
        (a.2.toString.length < b.2.toString.length || a.2.toString.length == b.2.toString.length &&
          Name.lt a.2 b.2))
  return rewrites.qsort lt

/-- Return all applicable library rewrites of `e`.
Note that the result may contain duplicate rewrites. These can be removed with `filterRewrites`. -/
def getRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← getCandidates e).mapM (checkAndSortRewriteLemmas e)

/-! ### Rewriting by lemmas from the same file -/

/-- Construct the `RefinedDiscrTree` of all lemmas defined in the current file. -/
def getLocalRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma) := do
  let env ← getEnv
  env.constants.map₂.foldlM (init := {}) fun tree name cinfo =>
    if isBadDecl name cinfo env then pure tree else updateDiscrTree tree
      ⟨name, false⟩ ⟨name, true⟩ cinfo.type


/-- Same as `getRewrites`, but for lemmas from the current file. -/
def getLocalRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← (← getLocalRewriteLemmas).getMatch e (unify := false)).mapM (checkAndSortRewriteLemmas e)

/-! ### Rewriting by hypotheses -/

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
def getHypotheses : MetaM (RefinedDiscrTree (FVarId × Bool)) := do
  let mut tree := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      tree ← updateDiscrTree tree (decl.fvarId, false) (decl.fvarId, true) decl.type
  return tree

/-- Return all applicable hypothesis rewrites of `e`. Similar to `getRewrites`. -/
def getHypothesisRewrites (e : Expr) : MetaM (Array (Array (Rewrite × FVarId))) := do
  (← (← getHypotheses).getMatch e (unify := false)).mapM <|
    Array.filterMapM fun (fvarId, symm) =>
      withCatchingRuntimeEx do
      try withoutCatchingRuntimeEx do
        OptionT.run do (·, fvarId) <$> checkRewrite (.fvar fvarId) e symm
      catch _ =>
        return none

/-! ### Filtering out duplicate lemmas -/

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


/-! ### User interface -/

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
    pasteString e
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
def tacticString (rw : Rewrite) (occ : Option Nat) (loc : Option Name) (isLemma : Bool)
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
  let proof ← printRewriteLemma rw.proof (isLemma && !rw.extraGoals.isEmpty)
  return mkRewrite occ rw.symm proof loc

open Widget ProofWidgets Jsx

/-- The structure with all data necessary for rendering a rewrite suggestion -/
structure RewriteInterface where
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- The rewrite tactic string that performs the rewrite -/
  tactic : String
  /-- The replacement expression obtained from the rewrite -/
  replacement : Expr
  /-- The replacement expression obtained from the rewrite -/
  replacementString : String
  /-- The extra goals created by the rewrite -/
  extraGoals : Array CodeWithInfos
  /-- The lemma name with hover information -/
  prettyLemma : CodeWithInfos
  /-- The type of the lemma -/
  lemmaType : Expr

/-- Construct the `RewriteInterface` from a `Rewrite`. -/
def Rewrite.toInterface (rw : Rewrite) (name : Name ⊕ FVarId) (occ : Option Nat) (loc : Option Name)
    (initNames : PersistentHashMap Name MVarId) : MetaM RewriteInterface := do
  let tactic ← tacticString rw occ loc (name matches .inl _) initNames
  let replacementString := Format.pretty (← ppExpr rw.replacement)
  let mut extraGoals := #[]
  for (mvarId, bi) in rw.extraGoals do
    if bi.isExplicit then
      let extraGoal ← ppExprTagged (← instantiateMVars (← mvarId.getType))
      extraGoals := extraGoals.push extraGoal
  match name with
  | .inl name =>
    let prettyLemma := match ← ppExprTagged (← mkConstWithLevelParams name) with
      | .tag tag _ => .tag tag (.text s!"{name}")
      | code => code
    let lemmaType := (← getConstInfo name).type
    return { rw with tactic, replacementString, extraGoals, prettyLemma, lemmaType }
  | .inr fvarId =>
    let prettyLemma ← ppExprTagged (.fvar fvarId)
    let lemmaType ← fvarId.getType
    return { rw with tactic, replacementString, extraGoals, prettyLemma, lemmaType }

/-- The kind of rewrite -/
inductive Kind where
  /-- A rewrite with a local hypothesis -/
  | hypothesis
  /-- A rewrite with a lemma from the current file -/
  | fromFile
  /-- A rewrite with a lemma from an imported file -/
  | fromCache

/-- Return the Interfaces for rewriting `e`, both filtered and unfiltered. -/
def getRewriteInterfaces (e : Expr) (occ : Option Nat) (loc : Option Name)
    (initNames : PersistentHashMap Name MVarId) :
    MetaM (Array (Array RewriteInterface × Kind) × Array (Array RewriteInterface × Kind)) := do
  let mut dedup := #[]
  let mut all := #[]
  for rewrites in ← getHypothesisRewrites e do
    let rewrites ← rewrites.mapM fun (rw, fvarId) => rw.toInterface (.inr fvarId) occ loc initNames
    all := all.push (rewrites, .hypothesis)
    dedup := dedup.push (← filterRewrites e rewrites (·.replacement), .hypothesis)

  for rewrites in ← getLocalRewrites e do
    let rewrites ← rewrites.mapM fun (rw, name) => rw.toInterface (.inl name) occ loc initNames
    all := all.push (rewrites, .fromFile)
    dedup := dedup.push (← filterRewrites e rewrites (·.replacement), .fromFile)

  for rewrites in ← getRewrites e do
    let rewrites ← rewrites.mapM fun (rw, name) => rw.toInterface (.inl name) occ loc initNames
    all := all.push (rewrites, .fromCache)
    dedup := dedup.push (← filterRewrites e rewrites (·.replacement), .fromCache)
  return (dedup, all)

/-- Render the matching side of the rewrite lemma.
This is shown at the header of each section of rewrite results. -/
def pattern {α} (type : Expr) (symm : Bool) (k : Expr → MetaM α) : MetaM α := do
  forallTelescope type fun _ e => do
    let some (lhs, rhs) := matchEqn? e | throwError "Expected equation, not {indentExpr e}"
    k (if symm then rhs else lhs)

/-- Render the given rewrite results. -/
def renderRewrites (e : Expr) (results : Array (Array RewriteInterface × Kind)) (init : Option Html)
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) (showNames : Bool) : MetaM Html := do
  let htmls ← results.filterMapM (renderSection showNames)
  let htmls := match init with
    | some html => #[html] ++ htmls
    | none => htmls
  if htmls.isEmpty then
    return <p> No rewrites found for <InteractiveCode fmt={← ppExprTagged e}/> </p>
  else
    return .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls
where
  /-- Render one section of rewrite results. -/
  renderSection (showNames : Bool) (sec : Array RewriteInterface × Kind) : MetaM (Option Html) := do
    let some head := sec.1[0]? | return none
    let suffix := match sec.2 with
      | .hypothesis => " (local hypotheses)"
      | .fromFile => " (local lemmas)"
      | .fromCache => ""
    return <details «open»={true}>
      <summary className="mv2 pointer">
        Pattern
        {← pattern head.lemmaType head.symm (return <InteractiveCode fmt={← ppExprTagged ·}/>)}
        {.text suffix}
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
              #[.text rw.replacementString] }
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

      let { userNames := initNames, .. } ← getMCtx
      let rootExpr ← loc.rootExpr
      let some (subExpr, occ) ← viewKAbstractSubExpr rootExpr loc.pos |
        return .text "expressions with bound variables are not supported"
      unless ← kabstractIsTypeCorrect rootExpr subExpr loc.pos do
        return .text <| "The selected expression cannot be rewritten, because the motive is " ++
          "not type correct. This usually occurs when trying to rewrite a term that appears " ++
          "as a dependent argument."
      let location ← loc.location

      let unfoldsHtml ← InteractiveUnfold.renderUnfolds subExpr occ location props.replaceRange doc

      let (filtered, all) ← getRewriteInterfaces subExpr occ location initNames
      let filtered ← renderRewrites subExpr filtered unfoldsHtml props.replaceRange doc false
      let all      ← renderRewrites subExpr all      unfoldsHtml props.replaceRange doc true
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
Click on the filter icon (top right) to switch to an unfiltered view that also shows lemma names.
-/
elab stx:"rw??" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash LibraryRewriteComponent.javascript)
    (pure $ json% { replaceRange : $range }) stx


/-- Represent a `Rewrite` as `MessageData`. -/
def Rewrite.toMessageData (rw : Rewrite) (name : Name) : MetaM MessageData := do
  let extraGoals ← rw.extraGoals.filterMapM fun (mvarId, bi) => do
    if bi.isExplicit then
      return some m! "⊢ {← mvarId.getType}"
    return none
  let list := [m! "{rw.replacement}"]
      ++ extraGoals.toList
      ++ [m! "{name}"]
  return .group <| .nest 2 <| "· " ++ .joinSep list "\n"

/-- Represent a section of rewrites as `MessageData`. -/
def SectionToMessageData (sec : Array (Rewrite × Name) × Bool) : MetaM (Option MessageData) := do
  let rewrites ← sec.1.toList.mapM fun (rw, name) => rw.toMessageData name
  let rewrites : MessageData := .group (.joinSep rewrites "\n")
  let some (rw, name) := sec.1[0]? | return none
  let head ← pattern (← getConstInfo name).type rw.symm (addMessageContext m! "{.}")
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
    let mut rewrites := #[]
    for rws in ← getLocalRewrites e do
      rewrites := rewrites.push (← filterRewrites e rws (·.1.replacement), true)
    for rws in ← getRewrites e do
      rewrites := rewrites.push (← filterRewrites e rws (·.1.replacement), false)
    let sections ← liftMetaM $ rewrites.filterMapM SectionToMessageData
    if sections.isEmpty then
      logInfo m! "No rewrites found for {e}"
    else
      logInfo (.joinSep sections.toList "\n\n")
