/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Tactic.Widget.InteractiveUnfold

/-!
# Point & click library rewriting

This file defines `rw??`, an interactive tactic that suggests rewrites for any expression selected
by the user.

We use a (lazy) `RefinedDiscrTree` to lookup a list of candidate rewrite lemmas.
We exclude lemmas defined in `Mathlib/Tactic/**` and `Init/Omega/**`, since these lemmas aren't
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

open Lean Meta

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The name of the lemma -/
  name : Name
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
deriving BEq, Inhabited

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : Option (Expr × Expr) :=
  match e.eq? with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- Return `true` if `s` and `t` are equal up to changing the `MVarId`s. -/
private def isSwap (t s : Expr) : Bool :=
  go t s |>.run' {}
where
  go (t s : Expr) : StateM (HashMap MVarId MVarId) Bool := do match t, s with
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ <&&> go b₁ b₂
  | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ <&&> go b₁ b₂
  | .mdata d₁ e₁      , .mdata d₂ e₂       => pure (d₁ == d₂) <&&> go e₁ e₂
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ <&&> go v₁ v₂ <&&> go b₁ b₂
  | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ <&&> go a₁ a₂
  | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => pure (n₁ == n₂ && i₁ == i₂) <&&> go e₁ e₂
  | .mvar mvarId₁     , .mvar mvarId₂      =>
    match (← get).find? mvarId₁ with
    | none =>
      modify (·.insert mvarId₁ mvarId₂ |>.insert mvarId₂ mvarId₁)
      return true
    | some mvarId =>
      return mvarId == mvarId₂
  | t                 , s                  => return t == s

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def addRewriteEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (Array (RefinedDiscrTree.Key × RefinedDiscrTree.LazyEntry RewriteLemma)) := do
  if name matches .str _ "injEq" | .str _ "sizeOf_spec" then
    return #[]
  let (_, _, eqn) ← forallMetaTelescope cinfo.type
  let some (lhs, rhs) := matchEqn? eqn | return #[]
  -- don't index lemmas of the form `a = ?b` where `?b` is a variable not appearing in `a`
  if let .mvar mvarId := lhs then
    if (rhs.findMVar? (· == mvarId)).isNone then
      return #[]
  if let .mvar mvarId := rhs then
    if (lhs.findMVar? (· == mvarId)).isNone then
      return #[]
  let result := (← RefinedDiscrTree.initializeLazyEntry lhs { name, symm := false } {}).toArray
  if isSwap lhs rhs then
    return result
  return result.appendList (← RefinedDiscrTree.initializeLazyEntry rhs { name, symm := true } {})


private abbrev ExtState := IO.Ref (Option (RefinedDiscrTree RewriteLemma))

private builtin_initialize ExtState.default : ExtState ←
  IO.mkRef none

private instance : Inhabited ExtState where
  default := ExtState.default

private initialize importedRewriteLemmasExt : EnvExtension ExtState ←
  registerEnvExtension (IO.mkRef none)



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

private def droppedKeys : List (List RefinedDiscrTree.Key) :=
  [[.star 0], [.const `Eq 3, .star 0, .star 1, .star 2]]

/-- Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded.
Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let constantsPerTask := 1000
  let matchResult ← RefinedDiscrTree.findImportMatches
    importedRewriteLemmasExt addRewriteEntry droppedKeys constantsPerTask e
  let candidates := matchResult.elts.reverse.concatMap id
  let excludedModules := getLibrarySearchExcludedModules (← getOptions)
  let env ← getEnv
  return candidates.map <|
    Array.filterMap fun rw =>
      env.const2ModIdx.find? rw.name >>= fun idx =>
      if containsPrefixOf excludedModules env.header.moduleNames[idx.toNat]!
      then none else some rw

/-- Get all potential rewrite lemmas from the current file. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getLocalCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let moduleTreeRef ← RefinedDiscrTree.createModuleTreeRef addRewriteEntry droppedKeys
  let matchResult ← RefinedDiscrTree.findModuleMatches moduleTreeRef e
  return matchResult.elts.reverse.concatMap id


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
    tryCatchRuntimeEx (do
        let thm ← mkConstWithFreshMVarLevels rw.name
        OptionT.run do (·, rw.name) <$> checkRewrite thm e rw.symm)
      fun _ =>
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

/-- Same as `getRewrites`, but for lemmas from the current file. -/
def getLocalRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← getLocalCandidates e).mapM (checkAndSortRewriteLemmas e)

/-! ### Rewriting by hypotheses -/

-- /-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
-- def getHypotheses : MetaM (RefinedDiscrTree (FVarId × Bool)) := do
--   let mut tree := {}
--   for decl in ← getLCtx do
--     if !decl.isImplementationDetail then
--       tree ← updateDiscrTree tree (decl.fvarId, false) (decl.fvarId, true) decl.type
--   return tree

-- /-- Return all applicable hypothesis rewrites of `e`. Similar to `getRewrites`. -/
-- def getHypothesisRewrites (e : Expr) : MetaM (Array (Array (Rewrite × FVarId))) := do
--   (← (← getHypotheses).getMatch e (unify := false)).mapM <|
--     Array.filterMapM fun (fvarId, symm) =>
--       withCatchingRuntimeEx do
--       try withoutCatchingRuntimeEx do
--         OptionT.run do (·, fvarId) <$> checkRewrite (.fvar fvarId) e symm
--       catch _ =>
--         return none

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
        filtered.anyM (isExplicitEq (replacement rw) <| replacement ·)) do
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
      |>.setBool pp.universes.name false
      |>.setBool pp.match.name false
      |>.setBool pp.instances.name false
      |>.setBool pp.unicode.fun.name true) do
    let (stx, _) ← delabCore e (delab := delabExplicit)
    return Format.pretty (← ppTerm stx) (width := 90) (indent := 2)
  else
    pasteString e
where
  /-- See `delabApp` and `delabAppCore`. -/
  delabExplicit : Delab := do
    let e ← getExpr
    let paramKinds ← getParamKinds e.getAppFn e.getAppArgs
    delabAppExplicitCore false e.getAppNumArgs (fun _ => delabConst) paramKinds

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

open Widget ProofWidgets Jsx Server

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
-- for rewrites in ← getHypothesisRewrites e do
--   let rewrites ← rewrites.mapM fun (rw, fvarId) => rw.toInterface (.inr fvarId) occ loc initNames
--   all := all.push (rewrites, .hypothesis)
--   dedup := dedup.push (← filterRewrites e rewrites (·.replacement), .hypothesis)

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
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) (showNames : Bool) :
    MetaM Html := do
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
    (pure <| json% { replaceRange : $range }) stx


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
  let head ← pattern (← getConstInfo name).type rw.symm (addMessageContext m! "{·}")
  return some <| "Pattern " ++ head ++ "\n" ++ rewrites

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
    let sections ← liftMetaM <| rewrites.filterMapM SectionToMessageData
    if sections.isEmpty then
      logInfo m! "No rewrites found for {e}"
    else
      logInfo (.joinSep sections.toList "\n\n")

end Mathlib.Tactic.LibraryRewrite
