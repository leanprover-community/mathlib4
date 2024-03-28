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
  d.insertEqn lhs rhs
    { name, symm := false, numParams := vars.size }
    { name, symm := true,  numParams := vars.size }

section Cache

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

end Cache



/-- Return all potential rewrite lemmata -/
def getCandidates (e : Expr) : MetaM (Array (Array RewriteLemma × Bool)) := do
  let localResults  ← (← getLocalRewriteLemmas ).getMatchWithScore e (unify := false)
  let cachedResults ← (← getCachedRewriteLemmas).getMatchWithScore e (unify := false)
  let allResults := localResults.map (·.1, true) ++ cachedResults.map (·.1, false)
  return allResults

structure Rewrite extends RewriteLemma where
  proof : Expr
  replacement : Expr
  extraGoals : Array (MVarId × BinderInfo)

/-- If `rwLemma` can be used to rewrite `e`, return the rewrite. -/
def checkLemma (rwLemma : RewriteLemma) (e : Expr) : MetaM (Option Rewrite) := do
  let thm ← try mkConstWithFreshMVarLevels rwLemma.name catch _ => return none
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
The boolean flag indicates whether the lemmata are from the current file. -/
def getRewrites (e : Expr) : MetaM (Array (Array Rewrite × Bool)) := do
  let candidates ← getCandidates e
  candidates.filterMapM fun (candidates, isLocal) => do
    let rewrites ← candidates.filterMapM (checkLemma · e)
    unless rewrites.isEmpty do
      return (rewrites, isLocal)
    return none

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
    return Format.pretty (← ppTerm stx) (indent := 2)
  else
    printToPaste e
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

structure RewriteInterface extends RewriteLemma where
  tactic : String
  replacement : String
  extraGoals : Array CodeWithInfos
  prettyLemma : CodeWithInfos

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
  return { rw with tactic, replacement, extraGoals, prettyLemma }

/-- Return the Interfaces for rewriting `e`, both filtered and unfiltered. -/
def getRewriteInterfaces (e : Expr) (occ : Option Nat) (loc : Option Name)
    (initNames : PersistentHashMap Name MVarId) :
    MetaM (Array (Array RewriteInterface × Bool) × Array (Array RewriteInterface × Bool)) := do
  let mut dedup := #[]
  let mut all := #[]
  for (rewrites, isLocal) in ← getRewrites e do
    let results ← rewrites.mapM (·.toInterface occ loc initNames)
    all := all.push (results, isLocal)
    let duplicates : HashMap String Name := results.foldl
      (init := HashMap.empty.insert (Format.pretty (← ppExpr e)) .anonymous) fun map rw =>
      if rw.extraGoals.isEmpty && !map.contains rw.replacement then
        map.insert rw.replacement rw.name
      else
        map
    let filtered := results.filter fun rw =>
        match duplicates.find? rw.replacement with
        | some name => name == rw.name
        | none      => true
    unless filtered.isEmpty do
      dedup := dedup.push (filtered, isLocal)
  return (dedup, all)

def RewriteLemma.pattern (rwLemma : RewriteLemma) : MetaM CodeWithInfos := do
  let cinfo ← getConstInfo rwLemma.name
  forallTelescope cinfo.type fun _ e => do
    let some (lhs, rhs) := matchEqn? e | throwError "Expected equation, not {indentExpr e}"
    let side := if rwLemma.symm then rhs else lhs
    ppExprTagged side

def renderRewrites (results : Array (Array RewriteInterface × Bool)) (init : Option Html)
    (range : Lsp.Range) (doc : FileWorker.EditableDocument) (showNames : Bool) : MetaM Html := do
  let htmls ← results.mapM (renderSection showNames)
  let htmls := match init with
      | some html => #[html] ++ htmls
      | none => htmls
  if htmls.isEmpty then
    return .text "No rewrites found."
  else
    return .element "div" #[("style", json% {"marginLeft" : "4px"})] htmls
where
  renderSection (showNames : Bool) (sec : Array RewriteInterface × Bool) : MetaM Html := do
    let some first := sec.1[0]? | return <div/>
    return <details «open»={true}>
      <summary className="mv2 pointer">
        {.text "Pattern "}
        <InteractiveCode fmt={← first.pattern}/>
        {.text (if sec.2 then " (local results)" else "")}
      </summary>
      {renderSectionCore showNames sec.1}
    </details>

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
      profileitM Exception "rw??" (← getOptions) do

        let { userNames := initNames, .. } ← getMCtx
        let some (subExpr, occ) ← viewKAbstractSubExpr (← loc.rootExpr) loc.pos |
          return .text "rw doesn't work on expressions with bound variables."
        let location ← loc.location

        let unfolds ← InteractiveUnfold.unfoldsWithTacticString subExpr occ location
        let unfoldsHtml ← if unfolds.isEmpty then pure none else
          InteractiveUnfold.renderDefinitions unfolds props.replaceRange doc

        let (filtered, all) ← getRewriteInterfaces subExpr occ location initNames
        let filtered ← renderRewrites filtered unfoldsHtml props.replaceRange doc false
        let all      ← renderRewrites all      unfoldsHtml props.replaceRange doc true
        return <FilterDetails
          message={"Rewrite suggestions:"}
          all={all}
          filtered={filtered}
          initiallyFiltered={true} />

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

-- def slow (n : Nat):Bool := (n.fold (init := #[]) (fun a b => #[a] ++ b)|>.size) == n
-- def t (x b:Bool) := (x,b)
-- @[inline] def g (n : Nat) : Bool → _ :=
--   let x : Bool :=  slow n
--   t x
-- def h ( n : Nat) :=
--   let y := g n
--   (y true, y false)
-- set_option profiler true
-- #eval g 30000 false
-- #eval h 30000
