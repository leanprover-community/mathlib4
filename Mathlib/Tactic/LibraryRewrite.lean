/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Anand Rao
-/
import Mathlib.Lean.Meta.RefinedDiscrTree
import Mathlib.Tactic.InteractiveUnfold

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

/-- The structure that we store in the `RefinedDiscrTree`. -/
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

def isBadModule (name : Name) : Bool :=
  (`Mathlib.Tactic).isPrefixOf name

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
def RewriteCache := Cache (RefinedDiscrTree RewriteLemma)

def RewriteCache.mk (init : Option (RefinedDiscrTree RewriteLemma) := none) : IO RewriteCache :=
  Cache.mk do
    match init with
    | some tree => return tree
    | none =>
      profileitM Exception "rw??: init cache" (← getOptions) do
        let env ← getEnv
        let mut tree := {}
        for moduleName in env.header.moduleNames, data in env.header.moduleData do
          if isBadModule moduleName then
            continue
          for cinfo in data.constants do
            tree ← updateDiscrTree cinfo.name cinfo tree
        return tree.mapArrays (·.qsort (· < ·))

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

def getCachedRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma) :=
  cachedData.get

def getLocalRewriteLemmas : MetaM (RefinedDiscrTree RewriteLemma) := do
  (← getEnv).constants.map₂.foldlM (init := {}) (fun tree n c => updateDiscrTree n c tree)

end



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
    |>.setBool `pp.match false
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

structure RewriteApplication extends RewriteLemma where
  tactic : String
  replacement : String
  extraGoals : Array CodeWithInfos
  prettyLemma : CodeWithInfos

def rewriteCall (rwLemma : RewriteLemma) (loc : SubExpr.GoalLocation) (subExpr : Expr)
    (occ : Option Nat) (initNames : PersistentHashMap Name MVarId) :
    MetaM (Option RewriteApplication) := do
  -- the lemma might not be imported, so we use a try-catch block here.
  let thm ← try mkConstWithFreshMVarLevels rwLemma.name catch _ => return none
  let (mvars, bis, eqn) ← forallMetaTelescope (← inferType thm)
  let some (lhs, rhs) := matchEqn? eqn | return none
  let (lhs, rhs) := if rwLemma.symm then (rhs, lhs) else (lhs, rhs)
  unless ← withReducible (isDefEq lhs subExpr) do return none

  let mut extraGoals := #[]
  let mut allAssigned := true
  let mut initNames := initNames
  for mvar in mvars, bi in bis do
    let mvarId := mvar.mvarId!
    -- we need to check that all instances can be synthesized
    if bi.isInstImplicit then
      let .some _ ← trySynthInstance (← mvarId.getType) | return none
      -- maybe check that the synthesized instance and `mvar` are `isDefEq`?
    else if !(← mvarId.isAssigned) then
      allAssigned := false
      let name ← mvarId.getTag
      -- if the userName has macro scopes, it comes from a non-dependent arrow,
      -- so we use `?_` instead
      if name.hasMacroScopes then
        mvarId.setTag `«_»
      else
        let name := getUnusedMVarName name initNames
        mvarId.setTag name
        initNames := initNames.insert name mvarId
      if bi.isExplicit then
        let extraGoal ← instantiateMVars (← mvarId.getType)
        extraGoals := extraGoals.push (← ppExprTagged extraGoal)

  let replacement := (← ppExprTagged (← instantiateMVars rhs)).stripTags
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
  -- we pretty print the lemma without `@` before the name
  let prettyLemma := match ← ppExprTagged (← mkConstWithLevelParams rwLemma.name) with
    | .tag tag _ => .tag tag (.text rwLemma.name.toString)
    | code => code
  return some { rwLemma with tactic, extraGoals, replacement, prettyLemma }

/-- The library results are displayed to the user in sections. Each section corresponds to
a particular pattern and to whether the lemma is defined in the file that the user is in. -/
structure Section where
  pattern : CodeWithInfos
  isLocal : Bool
  results : Array RewriteApplication


structure FilterDetailsProps where
  message : String
  filtered : Html
  all : Html
  initiallyFiltered : Bool
deriving RpcEncodable

/-- `FilterDetails` is a details component that has a button for switching between a filtered
and a non-filtered view. -/
@[widget_module]
def FilterDetails : Component FilterDetailsProps where
  javascript := include_str "LibraryRewrite" / "FilterDetails.js"

def renderFilterResults (results : Array Section × Array Section) (init : Option Html)
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) : Html :=
  let (filtered, all) := results;
  <FilterDetails
    message={"Rewrite suggestions:"}
    all={renderResults true all}
    filtered={renderResults false filtered}
    initiallyFiltered={true} />
where
  renderResults (showNames : Bool) (results : Array Section) : Html :=
    let htmls := results.map (renderSection showNames)
    let htmls := match init with
      | some html => #[html] ++ htmls
      | none => htmls
    if results.isEmpty then
      .text "No rewrites found."
    else
      .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls

  renderSection (showNames : Bool) (sec : Section) : Html :=
    <details «open»={true}>
      <summary className="mv2 pointer">
        {.text "Pattern "}
        <InteractiveCode fmt={sec.pattern}/>
        {.text (if sec.isLocal then " (local results)" else "")}
      </summary>
      {renderSectionCore showNames sec}
    </details>

  renderSectionCore (showNames : Bool)  (sec : Section): Html :=
    .element "ul" #[("style", json% { "padding-left" : "30px"})] <|
    sec.results.map fun rw =>
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

/-- Return all potenital rewrite lemmata -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma × Bool)) := do
  let localResults  ← (← getLocalRewriteLemmas ).getMatchWithScore e (unify := true)
  let cachedResults ← (← getCachedRewriteLemmas).getMatchWithScore e (unify := true)
  let allResults := localResults.map (·.1, true) ++ cachedResults.map (·.1, false)
  return allResults

def checkLemmata (ass : Array (Array RewriteLemma × Bool)) (loc : SubExpr.GoalLocation)
    (subExpr : Expr) (occ : Option Nat) (initNames : PersistentHashMap Name MVarId) :
    MetaM (Array Section × Array Section) := do
  let subExprString := (← ppExprTagged subExpr).stripTags
  let mut results := #[]
  let mut dedups := #[]
  for (as, isLocal) in ass do
    let mut bs := #[]
    for a in as do
      if let some b ← rewriteCall a loc subExpr occ initNames then
        bs := bs.push b
    if h : bs.size > 0 then
      let pattern ← bs[0].pattern
      results := results.push { pattern, isLocal, results := bs }
      bs := dedupLemmata bs subExprString
      if bs.size > 0 then
        dedups := dedups.push { pattern, isLocal, results := bs }
  return (dedups, results)
where
  /-- Remove duplicate lemmata and lemmata that do not change the expression. -/
  dedupLemmata (lemmata : Array RewriteApplication) (subExprString : String) :
      Array RewriteApplication :=
    let replacements : HashMap String Name := lemmata.foldl (init := .empty) fun map lem =>
      if lem.extraGoals.isEmpty && !map.contains lem.replacement then
        map.insert lem.replacement lem.name
      else
        map
    lemmata.filter fun lem =>
      if lem.replacement == subExprString then
        false
      else
        match replacements.find? lem.replacement with
        | some name => name == lem.name
        | none      => true

def getLibraryRewrites (loc : SubExpr.GoalsLocation) :
    ExceptT String MetaM (Array Section × Array Section) := do
  let { userNames := initNames, .. } ← getMCtx
  let e ← loc.rootExpr
  let subExpr ← Core.viewSubexpr loc.pos e
  if subExpr.hasLooseBVars then
    throwThe String "rw doesn't work on expressions with bound variables."
  let rwLemmas ← getCandidates subExpr
  let positions ← kabstractPositions subExpr e
  let occurrence := if positions.size == 1 then none else
    positions.findIdx? (· == loc.pos) |>.map (· + 1)
  checkLemmata rwLemmas loc.loc subExpr occurrence initNames

@[server_rpc_method_cancellable]
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
  goal.ctx.val.runMetaM {} do
    let md ← goal.mvarId.getDecl
    let lctx := md.lctx |>.sanitizeNames.run' {options := (← getOptions)}
    Meta.withLCtx lctx md.localInstances do
      profileitM Exception "libraryRewrite" (← getOptions) do
        let unfolds ← InteractiveUnfold.getDefinitions loc
        let unfolds := (InteractiveUnfold.renderDefinitions · props.replaceRange doc)
          <$> unfolds.toOption
        match ← getLibraryRewrites loc with
        | .ok results => return renderFilterResults results unfolds props.replaceRange doc
        | .error msg  => return .text msg

@[widget_module]
def LibraryRewrite : Component SelectInsertParams :=
  mk_rpc_widget% LibraryRewrite.rpc

/--
To use `rw??`, shift-click an expression in the tactic state.
This gives a list of rewrite suggestions for the selected expression.
Click on a suggestion to replace `rw??` by a tactic that performs this rewrite.
Click on the filter icon to switch to an unfiltered view that also shows the lemma names.
-/
elab stx:"rw??" : tactic => do
  let some range := (← getFileMap).rangeOfStx? stx | return
  Widget.savePanelWidgetInfo (hash LibraryRewrite.javascript)
    (pure $ json% { replaceRange : $range }) stx
