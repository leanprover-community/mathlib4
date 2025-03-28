/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Tactic.Widget.InteractiveUnfold
import ProofWidgets.Component.FilterDetails

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
- rewrites with fewer extra goals come first
- left-to-right rewrites come first
- shorter lemma names come first
- alphabetically ordered by lemma name

The lemmas are optionally filtered to avoid duplicate rewrites, or trivial rewrites. This
is controlled by the filter button on the top right of the results.

When a rewrite lemma introduces new goals, these are shown after a `⊢`.

-/

/-! ### Caching -/

namespace Mathlib.Tactic.LibraryRewrite

open Lean Meta RefinedDiscrTree

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RewriteLemma where
  /-- The name of the lemma -/
  name : Name
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
deriving BEq, Inhabited

instance : ToFormat RewriteLemma where
  format lem := f! "{if lem.symm then "← " else ""}{lem.name}"

/-- Return `true` if `s` and `t` are equal up to changing the `MVarId`s. -/
def isMVarSwap (t s : Expr) : Bool :=
  go t s {} |>.isSome
where
  /-- The main loop of `isMVarSwap`. Returning `none` corresponds to a failure. -/
  go (t s : Expr) (l : AssocList MVarId MVarId) : Option (AssocList MVarId MVarId) := do
  let isTricky e := e.hasExprMVar || e.hasLevelParam
  if isTricky t then
    guard (isTricky s)
    match t, s with
    -- Note we don't bother keeping track of universe level metavariables.
    | .const n₁ _       , .const n₂ _        => guard (n₁ == n₂); some l
    | .sort _           , .sort _            => some l
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ l >>= go b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _     => go d₁ d₂ l >>= go b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂       => guard (d₁ == d₂); go e₁ e₂ l
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => go t₁ t₂ l >>= go v₁ v₂ >>= go b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂         => go f₁ f₂ l >>= go a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂     => guard (n₁ == n₂ && i₁ == i₂); go e₁ e₂ l
    | .fvar fvarId₁     , .fvar fvarId₂      => guard (fvarId₁ == fvarId₂); some l
    | .lit v₁           , .lit v₂            => guard (v₁ == v₂); some l
    | .bvar i₁          , .bvar i₂           => guard (i₁ == i₂); some l
    | .mvar mvarId₁     , .mvar mvarId₂      =>
      match l.find? mvarId₁ with
      | none =>
        let l := l.insert mvarId₁ mvarId₂
        if mvarId₁ == mvarId₂ then
          some l
        else
          some <| l.insert mvarId₂ mvarId₁
      | some mvarId => guard (mvarId == mvarId₂); some l
    | _                 , _                  => none
  else
    guard (t == s); return l

/-- Try adding the lemma to the `RefinedDiscrTree`. -/
def addRewriteEntry (name : Name) (cinfo : ConstantInfo) :
    MetaM (List (RewriteLemma × List (Key × LazyEntry))) := do
  if name matches .str _ "injEq" | .str _ "sizeOf_spec" then return [] else
  let .const head _ := cinfo.type.getForallBody.getAppFn | return []
  if !(head == ``Eq || head == ``Iff) then return [] else
  setMCtx {}
  let (_,_,eqn) ← forallMetaTelescope cinfo.type
  let cont lhs rhs := do
    let badMatch e :=
      e.getAppFn.isMVar ||
      e.eq?.any fun (α, l, r) =>
        α.getAppFn.isMVar && l.getAppFn.isMVar && r.getAppFn.isMVar && l != r
    if badMatch lhs then
      if badMatch rhs then
        return []
      else
        return [({ name, symm := true }, ← initializeLazyEntryWithEta rhs)]
    else
      let result := ({ name, symm := false }, ← initializeLazyEntryWithEta lhs)
      if badMatch rhs || isMVarSwap lhs rhs then
        return [result]
      else
        return [result, ({ name, symm := true }, ← initializeLazyEntryWithEta rhs)]
  match eqn.eq? with
  | some (_, lhs, rhs) => cont lhs rhs
  | none => match eqn.iff? with
    | some (lhs, rhs) => cont lhs rhs
    | none => return []

/-- Try adding the local hypothesis to the `RefinedDiscrTree`. -/
def addLocalRewriteEntry (decl : LocalDecl) :
    MetaM (List ((FVarId × Bool) × List (Key × LazyEntry))) :=
  withReducible do
  let (_,_,eqn) ← forallMetaTelescope decl.type
  let cont lhs rhs := do
    let result := ((decl.fvarId, false), ← initializeLazyEntryWithEta lhs)
    return [result, ((decl.fvarId, true), ← initializeLazyEntryWithEta rhs)]
  match ← matchEq? eqn with
  | some (_, lhs, rhs) => cont lhs rhs
  | none => match eqn.iff? with
    | some (lhs, rhs) => cont lhs rhs
    | none => return []

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

/-- Get all potential rewrite lemmas from the imported environment.
By setting the `librarySearch.excludedModules` option, all lemmas from certain modules
can be excluded.
Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getImportCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let matchResult ← findImportMatches importedRewriteLemmasExt addRewriteEntry
    /-
    5000 constants seems to be approximately the right number of tasks
    Too many means the tasks are too long.
    Too few means less cache can be reused and more time is spent on combining different results.

    With 5000 constants per task, we set the `HashMap` capacity to 256,
    which is the largest capacity it gets to reach.
    -/
    (constantsPerTask := 5000) (capacityPerTask := 256) e
  let candidates := matchResult.elts.reverse.flatMap id
  let excludedModules := getLibrarySearchExcludedModules (← getOptions)
  let env ← getEnv
  return candidates.map <|
    Array.filter fun rw =>
      let moduleIdx := env.const2ModIdx[rw.name]!
      let moduleName := env.header.moduleNames[moduleIdx.toNat]!
      !excludedModules.any (·.isPrefixOf moduleName)

/-- Get all potential rewrite lemmas from the current file. Exclude lemmas from modules
in the `librarySearch.excludedModules` option. -/
def getModuleCandidates (e : Expr) : MetaM (Array (Array RewriteLemma)) := do
  let moduleTreeRef ← createModuleTreeRef addRewriteEntry
  let matchResult ← findModuleMatches moduleTreeRef e
  return matchResult.elts.reverse.flatMap id


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
  /-- Whether the rewrite introduces new metavariables with the replacement. -/
  makesNewMVars : Bool

/-- Extract the left and right hand sides of an equality or iff statement. -/
def matchEqn? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  pure <| match ← matchEq? e with
  | some (_, lhs, rhs) => some (lhs, rhs)
  | none => e.iff?

/-- If `thm` can be used to rewrite `e`, return the rewrite. -/
def checkRewrite (thm e : Expr) (symm : Bool) : MetaM (Option Rewrite) := do
  withTraceNodeBefore `rw?? (return m!
    "rewriting {e} by {if symm then "← " else ""}{thm}") do
  let (mvars, binderInfos, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) ← matchEqn? eqn | return none
  let (lhs, rhs) := if symm then (rhs, lhs) else (lhs, rhs)
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments before unifying
  let unifies ← withTraceNodeBefore `rw?? (return m! "unifying {e} =?= {lhs}")
    (withReducible (isDefEq lhs e))
  unless unifies do
    return none
  let lhs ← instantiateMVars lhs
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    return none
  let mut extraGoals := #[]
  for mvar in mvars, bi in binderInfos do
    -- we need to check that all instances can be synthesized
    if bi.isInstImplicit then
      let cls ← mvar.mvarId!.getType
      let synthesized ← withTraceNodeBefore `rw??
          (return m! "synthesising {cls}, and assigning the result to {mvar}") do
        let some inst ← synthInstance? cls | return false
        isDefEq inst mvar
      unless synthesized do
        return none
    else
      unless ← mvar.mvarId!.isAssigned do
        extraGoals := extraGoals.push (mvar.mvarId!, bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars := (replacement.findMVar? fun mvarId => mvars.any (·.mvarId! == mvarId)).isSome
  let proof ← instantiateMVars (mkAppN thm mvars)
  return some { symm, proof, replacement, extraGoals, makesNewMVars }

initialize
  registerTraceClass `rw??

/-- Try to rewrite `e` with each of the rewrite lemmas, and sort the resulting rewrites. -/
def checkAndSortRewriteLemmas (e : Expr) (rewrites : Array RewriteLemma) :
    MetaM (Array (Rewrite × Name)) := do
  let rewrites ← rewrites.filterMapM fun rw =>
    tryCatchRuntimeEx do
        let thm ← mkConstWithFreshMVarLevels rw.name
        Option.map (·, rw.name) <$> checkRewrite thm e rw.symm
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
def getImportRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← getImportCandidates e).mapM (checkAndSortRewriteLemmas e)

/-- Same as `getImportRewrites`, but for lemmas from the current file. -/
def getModuleRewrites (e : Expr) : MetaM (Array (Array (Rewrite × Name))) := do
  (← getModuleCandidates e).mapM (checkAndSortRewriteLemmas e)

/-! ### Rewriting by hypotheses -/

/-- Construct the `RefinedDiscrTree` of all local hypotheses. -/
def getHypotheses (except : Option FVarId) : MetaM (RefinedDiscrTree (FVarId × Bool)) := do
  let mut tree : PreDiscrTree (FVarId × Bool) := {}
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && except.all (· != decl.fvarId) then
      for (val, entries) in ← addLocalRewriteEntry decl do
        for (key, entry) in entries do
          tree := tree.push key (entry, val)
  return tree.toRefinedDiscrTree

/-- Return all applicable hypothesis rewrites of `e`. Similar to `getImportRewrites`. -/
def getHypothesisRewrites (e : Expr) (except : Option FVarId) :
    MetaM (Array (Array (Rewrite × FVarId))) := do
  let (results, _) ← (← getHypotheses except).getMatch e (unify := false) (matchRootStar := true)
  let results := results.elts
  results.flatMapM <| Array.mapM <|
    Array.filterMapM fun (fvarId, symm) =>
      tryCatchRuntimeEx do
        Option.map (·, fvarId) <$> checkRewrite (.fvar fvarId) e symm
      fun _ =>
        return none

/-! ### Filtering out duplicate lemmas -/

/-- Get the `BinderInfo`s for the arguments of `mkAppN fn args`. -/
def getBinderInfos (fn : Expr) (args : Array Expr) : MetaM (Array BinderInfo) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType.isForall do
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
  t.getAppNumArgs.allM fun i _ =>
    if bis[i]!.isExplicit then
      isExplicitEq tArgs[i]! sArgs[i]!
    else
      isDefEq tArgs[i]! sArgs[i]!

/-- Filter out duplicate rewrites or reflexive rewrites. -/
@[specialize]
def filterRewrites {α} (e : Expr) (rewrites : Array α) (replacement : α → Expr)
    (makesNewMVars : α → Bool) : MetaM (Array α) :=
  withNewMCtxDepth do
  let mut filtered := #[]
  for rw in rewrites do
    if makesNewMVars rw then continue
    if ← isExplicitEq (replacement rw) e then continue
    if ← filtered.anyM (isExplicitEq (replacement rw) <| replacement ·) then continue
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
    let delabAppFn (insertExplicit : Bool) : Delab := do
      let stx ← if (← getExpr).consumeMData.isConst then withMDatasOptions delabConst else delab
      if insertExplicit && !stx.raw.isOfKind ``Lean.Parser.Term.explicit then `(@$stx) else pure stx
    delabAppExplicitCore false e.getAppNumArgs delabAppFn paramKinds

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
  let proof ← printRewriteLemma rw.proof isLemma
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
  /-- Whether the rewrite introduces new metavariables with the replacement. -/
  makesNewMVars : Bool

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
def getRewriteInterfaces (e : Expr) (occ : Option Nat) (loc : Option Name) (except : Option FVarId)
    (initNames : PersistentHashMap Name MVarId) :
    MetaM (Array (Array RewriteInterface × Kind) × Array (Array RewriteInterface × Kind)) := do
  let mut filtr := #[]
  let mut all := #[]
  for rewrites in ← getHypothesisRewrites e except do
    let rewrites ← rewrites.mapM fun (rw, fvarId) => rw.toInterface (.inr fvarId) occ loc initNames
    all := all.push (rewrites, .hypothesis)
    filtr := filtr.push (← filterRewrites e rewrites (·.replacement) (·.makesNewMVars), .hypothesis)

  for rewrites in ← getModuleRewrites e do
    let rewrites ← rewrites.mapM fun (rw, name) => rw.toInterface (.inl name) occ loc initNames
    all := all.push (rewrites, .fromFile)
    filtr := filtr.push (← filterRewrites e rewrites (·.replacement) (·.makesNewMVars), .fromFile)

  for rewrites in ← getImportRewrites e do
    let rewrites ← rewrites.mapM fun (rw, name) => rw.toInterface (.inl name) occ loc initNames
    all := all.push (rewrites, .fromCache)
    filtr := filtr.push (← filterRewrites e rewrites (·.replacement) (·.makesNewMVars), .fromCache)
  return (filtr, all)

/-- Render the matching side of the rewrite lemma.
This is shown at the header of each section of rewrite results. -/
def pattern {α} (type : Expr) (symm : Bool) (k : Expr → MetaM α) : MetaM α := do
  forallTelescope type fun _ e => do
    let some (lhs, rhs) ← matchEqn? e | throwError "Expected equation, not {indentExpr e}"
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
      | .fromFile => " (lemmas from current file)"
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
        let extraGoals := rw.extraGoals.flatMap fun extraGoal =>
          #[<br/>, <strong className="goal-vdash">⊢ </strong>, <InteractiveCode fmt={extraGoal}/>]
        #[button] ++ extraGoals ++
          if showNames then #[<br/>, <InteractiveCode fmt={rw.prettyLemma}/>] else #[] }
      </li>

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
      let fvarId := loc.fvarId
      let location ← fvarId.mapM FVarId.getUserName

      let unfoldsHtml ← InteractiveUnfold.renderUnfolds subExpr occ location props.replaceRange doc

      let (filtered, all) ← getRewriteInterfaces subExpr occ location fvarId initNames
      let filtered ← renderRewrites subExpr filtered unfoldsHtml props.replaceRange doc false
      let all      ← renderRewrites subExpr all      unfoldsHtml props.replaceRange doc true
      return <FilterDetails
        summary={.text "Rewrite suggestions:"}
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
syntax (name := rw??Command) "#rw??" ("all")? term : command

open Elab
/-- Elaborate a `#rw??` command. -/
@[command_elab rw??Command]
def elabrw??Command : Command.CommandElab := fun stx =>
  withoutModifyingEnv <| Command.runTermElabM fun _ => do
  let e ← Term.elabTerm stx[2] none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← Term.levelMVarToParam (← instantiateMVars e)

  let filter := stx[1].isNone
  let mut rewrites := #[]
  for rws in ← getModuleRewrites e do
    let rws ← if filter then
      filterRewrites e rws (·.1.replacement) (·.1.makesNewMVars)
      else pure rws
    rewrites := rewrites.push (rws, true)
  for rws in ← getImportRewrites e do
    let rws ← if filter then
      filterRewrites e rws (·.1.replacement) (·.1.makesNewMVars)
      else pure rws
    rewrites := rewrites.push (rws, false)

  let sections ← liftMetaM <| rewrites.filterMapM SectionToMessageData
  if sections.isEmpty then
    logInfo m! "No rewrites found for {e}"
  else
    logInfo (.joinSep sections.toList "\n\n")

end Mathlib.Tactic.LibraryRewrite
