/-
Copyright (c) 2025 Vlad Tsyrklevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vlad Tsyrklevich
-/
-- TODO
import Lean
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

/-!
# The "generalizeTypeClass" linter

This linter looks for opportunities to generalize type classes in theorem declarations, by trying
to re-elaborate the declaration with every type class replaced by its parent type classes and seeing
if it is successful.

TODO:
- Filter out IsCancelAdd
- Filter out Algebra with what Eric said in https://github.com/leanprover-community/mathlib4/pull/22566#discussion_r1980088892
- IsTopologicalRing/Semiring?

Another way we could handle this is to write linters that test for these meaningless generalizations, and then have your tool refuse to generalize them if the results give a linter warning



TODO:
- The linter has one large gap: it does not look at type classes pulled in via `variable` blocks.
- Fails:
section SectionTest
variable [Child]
/-- info: Generalize type class: Parent -/
--#guard_msgs in
theorem FAIL : False := Parent.parent_thm
end SectionTest
-/

namespace Mathlib.Linter

/--
The "generalizeTypeClass" linter emits suggestions on type classes specified in theorem definitions
that could use a more general type class.
-/
register_option linter.generalizeTypeClass : Bool := {
  defValue := true -- TODO
  descr := "enable the generalize type class linter"
}

namespace GeneralizeTypeClass

open Lean Elab Command Term Meta

scoped instance : MonadBacktrack Lean.Elab.Command.State CommandElabM where
  saveState      := get
  restoreState s := set s
-- TODO debugging
--  restoreState s := modify fun x => { s with messages := x.messages }

-- TODO
deriving instance Repr for ConstantVal, TheoremVal, StructureParentInfo, StructureInfo
deriving instance Repr for AxiomVal, InductiveVal
deriving instance Repr for LocalInstance

partial def filterAux (p : Syntax → Bool) : Syntax → Array Syntax
  | stx@(Syntax.node _ _ args) => (if p stx then #[stx] else #[]) ++ args.flatMap (filterAux p)
  | stx                        => if p stx then #[stx] else #[]

def _root_.Lean.Syntax.filter (stx : Syntax) (p : Syntax → Bool) : Array Syntax :=
  filterAux p stx

def matchNodeName (n : Name) : Syntax → Bool
  | Syntax.node _ kind _ => kind == n
  | _ => false

def getStruct (n : Name) : CommandElabM (Option StructureInfo) := do
  if let some struct := getStructureInfo? (← getEnv) n then
    return struct
  try
    return getStructureInfo? (← getEnv) (← Lean.getConstInfoInduct n).name
  catch _ =>
    return none

def moreGeneralizations : Std.HashMap Name (List Name) := Std.HashMap.ofList [
  (`Module, [`MulActionWithZero]),
  (`DistribMulAction, [`SMulZeroClass, `DistribSMul]),
  (`MulZeroClass, [`SMulWithZero]),
  (`MulActionWithZero, [`SMulWithZero]),
  (`MonoidWithZero, [`MulActionWithZero]),

  (`Group, [`DivisionMonoid, `CancelMonoid]),
  (`AddGroup, [`SubtractionMonoid, `AddCancelMonoid]),
  (`CommGroup, [`CancelCommMonoid, `DivisionCommMonoid]),
  (`AddCommGroup, [`AddCancelCommMonoid, `SubtractionCommMonoid]),

  (`CommSemiring, [`NonUnitalCommSemiring, `CommMonoidWithZero]),
  (`CommRing, [`CommSemiring, `NonUnitalCommRing, `AddCommGroupWithOne]),
  (`DivisionRing, [`DivisionSemiring]),
  (`Field, [`Semifield]),
  (`NonUnitalCommRing, [`NonUnitalCommSemiring]),
  (`Ring, [`NonUnitalRing, `NonAssocRing]),

  (`NormedDivisionRing, [`NormedRing]),
  (`DenselyNormedField, [`NontriviallyNormedField]),
  (`NormedField, [`NormedDivisionRing]),
  (`NormedField, [`NormedCommRing]),

  (`CompleteLattice, [`BoundedOrder]),
  (`CompleteLinearOrder, [`LinearOrder]),

  (`OrderedRing, [`OrderedSemiring]),
  (`OrderedCommRing, [`OrderedCommSemiring]),
  (`StrictOrderedCommSemiring, [`OrderedCommSemiring]),
  (`StrictOrderedSemiring, [`OrderedSemiring]),
  (`StrictOrderedRing, [`OrderedRing, `StrictOrderedSemiring]),
  (`StrictOrderedCommRing, [`OrderedCommRing, `StrictOrderedCommSemiring]),
  (`LinearOrderedRing, [`LinearOrderedSemiring, `LinearOrderedAddCommGroup]),
  (`LinearOrderedCommRing, [`StrictOrderedCommRing, `LinearOrderedCommSemiring]),

  (`T1Space, [`T0Space]),
  (`T2Space, [`T1Space]),
  (`T25Space, [`T2Space]),
  (`T3Space, [`T25Space]),
  (`T35Space, [`T3Space]),
  (`T4Space, [`T35Space]),
  (`T5Space, [`T4Space]),
  (`T6Space, [`T5Space]),
  (`CompletelyRegularSpace, [`RegularSpace]),
  (`PerfectlyNormalSpace, [`CompletelyNormalSpace]),
  (`CompletelyNormalSpace, [`NormalSpace]),
  (`PathConnectedSpace, [`ConnectedSpace]),
  (`IrreducibleSpace, [`ConnectedSpace]),
  (`PreirreducibleSpace, [`PreconnectedSpace]),
  (`R1Space, [`R0Space]),
 ]

-- TODO: Verify they're not typos/exist

def generalizationsFor (n : Name) : CommandElabM (List Name) := do
  let some st ← getStruct n | return []
  let parents := st.parentInfo.map (·.structName)
  return parents.toList ++ moreGeneralizations.getD n []

partial def checkTheoremConsistent (e : Expr) : CommandElabM (Bool) := do
  --logInfo s!"THM VAL (2): {repr e}"
  -- instance name → class name
  let mut classes : Std.HashMap Name (List Name) := {}
  for classType in getHeadBinderTypes e do
    --logInfo s!"  -> {repr classType}"
    if !classType.isApp || classType.getAppFn.constName?.isNone then continue

    let className := classType.getAppFn.constName!
    let args := classType.getAppArgs
    if args.size == 0 then continue

    --logInfo s!"-- {classType.getAppFn} || {repr className} || {args[0]!.constName} // {args.size}: {repr args}"
    -- TODO check we're not overwriting
    let typeName := args[0]!.constName
    if !classes.contains typeName then
      classes := classes.insert typeName List.nil
    classes := classes.insert typeName (className :: classes[typeName]!)

    --logInfo s!"=====> {args}"
    if className == `Module then
      if args.size < 2 then
        logError s!"__2 {args.size}"
        continue
--      logInfo s!"<><> {repr args[0]!.constName}"
      if !classes.contains args[0]!.constName || !classes.contains args[1]!.constName then
        logWarning s!"1111 {repr args[0]!} / {repr args[1]!} / {repr classes}"
        continue
      let RType := classes[args[0]!.constName]!
      let MType := classes[args[1]!.constName]!
      if !(← MType.anyM (isA · `AddCommGroup)) && (← RType.anyM (isA · `Ring)) then
        logWarning s!"23232 {repr args[0]!} / {repr args[1]!} / {repr classes} // {RType} + {MType}"
        return false
--      if MType.contains `AddCommMonoid && !RType.any (·.toString.endsWith "Semiring") then
--        logWarning s!"22222 {repr args[0]!} / {repr args[1]!} / {repr classes} // {RType} + {MType}"
--        return false
    else if className == `Algebra then
      if args.size < 2 then
        logError s!"__1 {args.size}"
        continue
      if !classes.contains args[0]!.constName || !classes.contains args[1]!.constName then
        logWarning s!"3333 {repr args[0]!} / {repr args[1]!} / {repr classes}"
        continue
      let RType := classes[args[0]!.constName]!
      let AType := classes[args[1]!.constName]!
      if (← RType.anyM (isA · `Ring)) && !(← AType.anyM (isA · `Ring)) then
        logWarning s!"4141 {repr args[0]!} / {repr args[1]!} / {repr classes} // {RType} + {AType}"
        return false
--      if RType.any (·.toString.endsWith "Ring") && AType.any (·.toString.endsWith "Semiring") then
--        logWarning s!"4444 {repr args[0]!} / {repr args[1]!} / {repr classes} // {RType} + {AType}"
--        return false

  --logInfo s!"55555 {repr classes}"
  for ⟨k, v⟩ in classes.toList do
    if v.contains `IsTopologicalSemiring && !v.contains `IsTopologicalRing && ((← v.anyM (isA · `NonUnitalNonAssocRing)) || (← v.anyM (isA · `Ring))) then
      logWarning s!"5151 {k} {repr v}"
      return false
--    if v.contains `IsTopologicalSemiring && v.any (·.toString.endsWith "Ring") then
--      logWarning s!"555 {k} {repr v}"
--      return false

  return true
where
  getHeadBinderTypes : Expr → List Expr
    | .forallE name type body _ => type :: getHeadBinderTypes (body.instantiate1 (mkConst name))
    | .lam name type body _ => type :: getHeadBinderTypes (body.instantiate1 (mkConst name))
    | _ => List.nil
  isA (c p : Name) : CommandElabM Bool := do
    if c == p then return true
    if let some cStruct ← getStruct c then
      cStruct.parentInfo.anyM (isA ·.structName p)
    else
      return false

syntax (name := generalize_type_class_theorem) (priority := default + 2) declModifiers
  group(("lemma" <|> "theorem") declId ppIndent(declSig) declVal) : command

@[command_elab generalize_type_class_theorem]
partial def generalizeTypeClass : CommandElab := withSetOptionIn fun stx => do
  -- We want to elaborate the theorem to look at its type, but then restore the previous state
  -- when we re-elaborate it.
  let before_state := ← get
  elabTheorem stx
  unless Linter.getLinterValue linter.generalizeTypeClass (← getOptions) do
    return
  -- Skip generalization if there are no type classes in the declaration
  let some _ := stx.find? (matchNodeName `Lean.Parser.Term.instBinder) | return
  let some declId := stx.find? (matchNodeName `Lean.Parser.Command.declId) | return
  let name := declId.getArg 0 |>.getId
  let mut thm_name :=
    if let `_root_ :: rest := name.components then
      rest.foldl (· ++ ·) default
    else (← getCurrNamespace) ++ name
  if stx.find? (matchNodeName `Lean.Parser.Command.private) |>.isSome then
    thm_name := mkPrivateName (← get).env thm_name
--  let some info := (← get).env.constants.find? thm_name | return
--  if !(← checkTheoremConsistent info.value!) then
--    logInfo s!"Not consistent"
-- TODO: Check for synthethic sorry here
  let some declSig := stx.find? (matchNodeName `Lean.Parser.Command.declSig) | return
  for inst in declSig.getArg 0 |>.getArgs do
    if inst.getKind == `Lean.Parser.Term.instBinder then
      let results ← match inst with
        | `(Lean.Parser.Term.instBinder| [$_ : $ty]) =>
            generalize stx ty.raw thm_name before_state
        | `(Lean.Parser.Term.instBinder| [$ty]) =>
            generalize stx ty.raw thm_name before_state
        | _ => throwError "unexpected instBinder"
      if results.length > 0 then
        -- TODO: Instead, perform the replacement in the signature, elab, and then see if given those type classes
        -- the original type class can still be synth'ed.
        let replaceInst (arr : Array Syntax) := arr.filterMap (fun x =>
          if x != inst || x.getHeadInfo != inst.getHeadInfo then some x else none)
        let newStx := stx.rewriteBottomUp (fun s => match s with
          | Syntax.node _ _ _ => s.modifyArgs replaceInst
          | _ => s)
        if let some res ← backtrackTryElab newStx thm_name before_state then
          if !res.value.hasSyntheticSorry then
            logWarning s!"Skipping generalization, deleting type class does nothing: {inst} {thm_name}"
            continue
      for ⟨replacement, type⟩ in results.eraseDups do
        let some id := type.find? (·.isIdent) | throwError "bad type identifier"
        logInfo s!"Replacement. theorem={thm_name} old={id.getId} new={replacement} loc={repr id.getRange?}"
        let suggestion : Lean.Meta.Tactic.TryThis.Suggestion :=
          { suggestion := replacement.getString!
            toCodeActionTitle? := .some (fun _ => s!"Generalize type class: {name.getString!}")}
        liftTermElabM <|
          Tactic.TryThis.addSuggestion id suggestion (header := "Generalize type class: ")
where
  elabTheorem (stx : Syntax) := do
    -- TODO: Use just raw elabCommand here/mathlib's lemma syntax instead of rolling my own?
    let stx := stx.modifyArg 1 fun stx =>
      let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
      stx.setKind ``Parser.Command.theorem
    elabCommand <| stx.setKind ``Parser.Command.declaration
  backtrackTryElab (stx : Syntax) (thm_name : Name) (before_state : Command.State) :
      CommandElabM (Option TheoremVal) := do
    withoutModifyingState do
      set { before_state with messages := {} }
      elabTheorem stx
      -- Another attribute/linter may complain even if the theorem compiles
      if (← get).messages.hasErrors then return none
      let some info := (← get).env.constants.find? thm_name | return none
      match info with
      | .thmInfo val => return val
      | .axiomInfo _ =>
        -- This can happen when a theorem with a recursive invocation can no longer be proven to
        -- terminate.
        return none
      | _ => throwError "unexpected ConstantInfo type"
  checkResynthesis (thm : Expr) (typeStx : Syntax) : TermElabM (Bool) := do
    lambdaTelescope thm fun _ _ ↦ do
      let typeclass ← elabType typeStx
      return (← synthInstance? typeclass).isSome
  generalizeAux (thm_stx id : Syntax) (thm_name structName : Name) (before_state : Command.State)
      (typeStx :Syntax) :
      CommandElabM (List Name) := do
    let mut results := List.nil
    for generalStruct in ← generalizationsFor structName do
      let replaceInst (arr : Array Syntax) := arr.map (fun x =>
        if x != id || x.getHeadInfo != id.getHeadInfo then x else mkIdent generalStruct)
      let newStx := thm_stx.rewriteBottomUp (fun s => match s with
        | Syntax.node _ _ _ => s.modifyArgs replaceInst
        | _ => s)
      if let some res ← backtrackTryElab newStx thm_name before_state then
        if res.value.hasSyntheticSorry then continue
        if !(← checkTheoremConsistent res.value) then
          logWarning s!"Skipping due to inconsistency thm={thm_name} struct={structName} parent={generalStruct}."
          continue
        if ← liftTermElabM <| checkResynthesis res.value typeStx then
          logWarning s!"Skipping generalization due to re-synthesis thm={thm_name} struct={structName} parent={generalStruct}."
          continue
        let next_dfs ← generalizeAux thm_stx id thm_name generalStruct before_state typeStx
        if next_dfs.length > 0 then
          results := next_dfs ++ results
        else
          results := results ++ [generalStruct]
    return results
  generalize (thm_stx type_stx : Syntax) (thm_name : Name) (before_state : Command.State) :
      CommandElabM (List (Name × Syntax)) := do
    let some id := type_stx.find? (·.isIdent) | throwError "bad type identifier"
    let results ← generalizeAux thm_stx id thm_name id.getId before_state type_stx
    return results.map (⟨·, type_stx⟩)

end GeneralizeTypeClass
end Mathlib.Linter
