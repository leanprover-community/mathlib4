/-
Copyright (c) 2026 Cody Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cody Mitchell
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public meta import Mathlib.Util.AddRelatedDecl

/-!
# The `@[to_subgroupOf]` attribute

Adding `@[to_subgroupOf]` to a theorem generates a sibling theorem whose ambient group is restricted
to an ambient subgroup `K : Subgroup G`, replacing subgroup binders `H : Subgroup G` by
`H.subgroupOf K`.
-/

public meta section

open Lean Meta Elab

namespace Mathlib.Tactic.ToSubgroupOf

/-- `@[to_subgroupOf foo]` uses `foo` as the generated theorem name. -/
syntax (name := to_subgroupOf) "to_subgroupOf" (ppSpace ident)? optAttrArg : attr

private def subgroupAmbient? (type : Expr) : Option Expr :=
  match type.getAppFnArgs with
  | (`Subgroup, args) => args[0]?
  | _ => none

private def isGroupInstanceOfAmbient (ambient : Expr) (type : Expr) : Bool :=
  match type.getAppFnArgs with
  | (`Group, #[arg]) => arg == ambient
  | _ => false

private def findExprIdx? (xs : Array Expr) (x : Expr) : Option Nat :=
  xs.findIdx? (· == x)

private def replaceWith (e : Expr) (olds news : Array Expr) : Expr :=
  e.replaceFVars olds news

private def carrierLevel (carrier : Expr) : MetaM Level := do
  let type ← whnf (← inferType carrier)
  let .sort u := type |
    throwError "expected a type-valued binder while building `to_subgroupOf`"
  pure <| match u with
    | .succ v => v
    | _ => u

private def mkSubgroupType (ambient groupInst : Expr) : MetaM Expr := do
  pure <| mkAppN (.const ``Subgroup [← carrierLevel ambient]) #[ambient, groupInst]

private def mkSubgroupCarrierSort (K : Expr) : MetaM Expr := do
  ensureIsSort K

private def mkSubgroupCarrierAndInst (ambient groupInst K : Expr) : MetaM (Expr × Expr) := do
  let toGroup := .const ``Subgroup.toGroup [← carrierLevel ambient]
  let KInst := mkAppN toGroup #[ambient, groupInst, K]
  let KSort ← mkSubgroupCarrierSort K
  pure (KSort, KInst)

private def lookupMapped? (olds news : Array Expr) (x : Expr) : Option Expr := do
  let idx ← findExprIdx? olds x
  news[idx]?

private def lookupMapped! (olds news : Array Expr) (x : Expr) : MetaM Expr :=
  match lookupMapped? olds news x with
  | some y => pure y
  | none => throwError "internal error: missing translated binder for {x}"

private structure BuildState where
  newBinders : Array Expr := #[]
  binderOlds : Array Expr := #[]
  binderNews : Array Expr := #[]
  imageOlds : Array Expr := #[]
  imageNews : Array Expr := #[]
  ambientPos : Nat
  instPos? : Option Nat := none
  K? : Option Expr := none

private def BuildState.pushBinder (st : BuildState) (oldBinder newBinder image : Expr)
    (isAmbient : Bool := false) (isGroupInst : Bool := false) : BuildState :=
  let pos := st.imageNews.size
  { st with
    newBinders := st.newBinders.push newBinder
    binderOlds := st.binderOlds.push oldBinder
    binderNews := st.binderNews.push newBinder
    imageOlds := st.imageOlds.push oldBinder
    imageNews := st.imageNews.push image
    ambientPos := if isAmbient then pos else st.ambientPos
    instPos? := if isGroupInst then some pos else st.instPos? }

private def analyzeBinders (xs : Array Expr) : MetaM (Expr × Nat × Nat × Array Nat × Nat) := do
  let mut subgroupIndices : Array Nat := #[]
  let mut ambients : Array Expr := #[]
  for i in [:xs.size] do
    let x := xs[i]!
    let xType := (← getFVarLocalDecl x).type
    if let some ambient := subgroupAmbient? xType then
      unless ambient.isFVar do
        throwError "`to_subgroupOf` only supports subgroup binders over a free \
          ambient group type"
      subgroupIndices := subgroupIndices.push i
      ambients := ambients.push ambient
  let some firstSubgroupIdx := subgroupIndices[0]? |
    throwError "`to_subgroupOf` requires at least one binder of type `Subgroup G`"
  let ambient := ambients[0]!
  for ambient' in ambients do
    unless ambient' == ambient do
      throwError "`to_subgroupOf` currently supports a single ambient group type"
  let some ambientIdx := findExprIdx? xs ambient |
    throwError "internal error: ambient group binder is missing from the theorem telescope"
  let mut groupInstIndices : Array Nat := #[]
  for i in [:xs.size] do
    let x := xs[i]!
    let xType := (← getFVarLocalDecl x).type
    if isGroupInstanceOfAmbient ambient xType then
      groupInstIndices := groupInstIndices.push i
  let some groupInstIdx := groupInstIndices[0]? |
    throwError "`to_subgroupOf` requires an explicit `[Group G]` binder"
  if groupInstIndices.size > 1 then
    throwError "`to_subgroupOf` currently supports a single `[Group G]` binder"
  let ambientId := ambient.fvarId!
  let groupInstId := xs[groupInstIdx]!.fvarId!
  let mut insertIdx := firstSubgroupIdx
  for i in [:firstSubgroupIdx] do
    if i != ambientIdx && i != groupInstIdx then
      let x := xs[i]!
      let xType := (← getFVarLocalDecl x).type
      if xType.containsFVar ambientId || xType.containsFVar groupInstId then
        insertIdx := i
        break
  unless ambientIdx < insertIdx do
    throwError "`to_subgroupOf` requires the ambient group type binder to occur before \
      translated binders"
  unless groupInstIdx < insertIdx do
    throwError "`to_subgroupOf` requires the `[Group G]` binder to occur before translated binders"
  pure (ambient, ambientIdx, groupInstIdx, subgroupIndices, insertIdx)

private partial def buildTranslatedValue (value : Expr) (xs : Array Expr)
    (ambient : Expr) (ambientIdx : Nat) (groupInstIdx : Nat)
    (subgroupIndices : Array Nat) (insertIdx : Nat) : MetaM Expr := do
  let subgroupBinders := subgroupIndices.map (xs[·]!)
  let rec go (i : Nat) (st : BuildState) : MetaM Expr := do
    if i == insertIdx && st.K?.isNone then
      let ambient' ← lookupMapped! st.binderOlds st.binderNews ambient
      let groupInst' ← lookupMapped! st.binderOlds st.binderNews xs[groupInstIdx]!
      let subgroupTy ← mkSubgroupType ambient' groupInst'
      withLocalDecl `K .default subgroupTy fun K => do
        let (KSort, KInst) ← mkSubgroupCarrierAndInst ambient' groupInst' K
        let imageNews := st.imageNews.set! st.ambientPos KSort
        let imageNews := match st.instPos? with
          | some pos => imageNews.set! pos KInst
          | none => imageNews
        let st := { st with
          newBinders := st.newBinders.push K
          imageNews := imageNews
          K? := some K }
        go i st
    else if i < xs.size then
      let x := xs[i]!
      let decl ← getFVarLocalDecl x
      let isSubgroupBinder := subgroupBinders.any (· == x)
      let domain ←
        if isSubgroupBinder || i == ambientIdx || i == groupInstIdx then
          instantiateMVars <| replaceWith decl.type st.binderOlds st.binderNews
        else
          instantiateMVars <| replaceWith decl.type st.imageOlds st.imageNews
      withLocalDecl decl.userName decl.binderInfo domain fun x' => do
        let image ←
          if i == ambientIdx || i == groupInstIdx then
            pure x'
          else if isSubgroupBinder then
            let some K := st.K? |
              throwError "internal error: subgroup binders appeared before the ambient subgroup \
                binder"
            let ambient' ← lookupMapped! st.binderOlds st.binderNews ambient
            let groupInst' ← lookupMapped! st.binderOlds st.binderNews xs[groupInstIdx]!
            let subgroupOf := .const ``Subgroup.subgroupOf [← carrierLevel ambient']
            pure <| mkAppN subgroupOf #[ambient', groupInst', x', K]
          else
            pure x'
        let st :=
          st.pushBinder x x' image (isAmbient := i == ambientIdx) (isGroupInst := i == groupInstIdx)
        go (i + 1) st
    else
      let sourceArgs ← xs.mapM fun x => lookupMapped! st.imageOlds st.imageNews x
      let sourceApp := mkAppN value sourceArgs
      mkLambdaFVars st.newBinders sourceApp
  go 0 { ambientPos := 0 }

/-- Translate a theorem value to its `subgroupOf` form. -/
def toSubgroupOfExpr (value : Expr) : MetaM Expr := do
  withLCtx {} {} do
    let type ← inferType value
    forallTelescope type fun xs _body => do
      let (ambient, ambientIdx, groupInstIdx, subgroupIndices, insertIdx) ← analyzeBinders xs
      buildTranslatedValue value xs ambient ambientIdx groupInstIdx subgroupIndices insertIdx

private def targetName (src : Name) (name? : Option Syntax) : Name :=
  match name? with
  | some stx => Name.updatePrefix stx.getId src.getPrefix
  | none => src.appendAfter "_subgroupOf"

initialize registerBuiltinAttribute {
  name := `to_subgroupOf
  descr := "generate a theorem whose ambient group is restricted by `Subgroup.subgroupOf`"
  applicationTime := .afterCompilation
  add := fun src ref kind => match ref with
  | `(attr| to_subgroupOf $[$name:ident]? $optAttr) => MetaM.run' do
      if kind != AttributeKind.global then
        throwError "`to_subgroupOf` can only be used as a global attribute"
      let tgt := targetName src name
      addRelatedDecl src tgt ref optAttr
        (docstringPrefix? := s!"`subgroupOf` form of `{src}`") (hoverInfo := true)
        fun value levels => do
          pure (← toSubgroupOfExpr value, levels)
  | _ => throwUnsupportedSyntax }

end Mathlib.Tactic.ToSubgroupOf
