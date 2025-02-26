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

syntax (name := generalize_type_class_theorem) (priority := default + 2) declModifiers
  group(("lemma" <|> "theorem") declId ppIndent(declSig) declVal) : command

partial def filterAux (p : Syntax → Bool) : Syntax → Array Syntax
  | stx@(Syntax.node _ _ args) => (if p stx then #[stx] else #[]) ++ args.flatMap (filterAux p)
  | stx                        => if p stx then #[stx] else #[]

def _root_.Lean.Syntax.filter (stx : Syntax) (p : Syntax → Bool) : Array Syntax :=
  filterAux p stx

def matchNodeName (n : Name) : Syntax → Bool
  | Syntax.node _ kind _ => kind == n
  | _ => false

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
        let replaceInst (arr : Array Syntax) := arr.filterMap (fun x =>
          if x != inst then some x else none)
        let newStx := stx.rewriteBottomUp (fun s => match s with
          | Syntax.node _ _ _ => s.modifyArgs replaceInst
          | _ => s)
        if let some res ← backtrackTryElab newStx thm_name before_state then
          if !res.value.hasSyntheticSorry then
            logInfo s!"SKIPPING {inst} {thm_name}"
            continue
      for ⟨replacement, type⟩ in results.eraseDups do
        if ← badGeneralization stx type replacement then
          continue
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
  generalizeAux (thm_stx id : Syntax) (thm_name structName : Name) (before_state : Command.State) :
      CommandElabM (List Name) := do
    let mut optstruct := getStructureInfo? (← getEnv) structName
    if optstruct.isNone then
      try
        optstruct := getStructureInfo? (← getEnv) (← Lean.getConstInfoInduct structName).name
      catch _ =>
        return []
    let some struct := optstruct | return []
    let mut results := List.nil
    for p in struct.parentInfo do
      let replaceInst (arr : Array Syntax) := arr.map (fun x =>
        if x != id then x else mkIdent p.structName)
      let newStx := thm_stx.rewriteBottomUp (fun s => match s with
        | Syntax.node _ _ _ => s.modifyArgs replaceInst
        | _ => s)
      if let some res ← backtrackTryElab newStx thm_name before_state then
        -- Don't generalize if the number of foralls in the type increases as the theorem may just
        -- be pulling another type class from the variable block
        if !res.value.hasSyntheticSorry then
          let next_dfs ← generalizeAux thm_stx id thm_name p.structName before_state
          if next_dfs.length > 0 then
            results := next_dfs ++ results
          else
            results := results ++ [p.structName]
    return results
  generalize (thm_stx type_stx : Syntax) (thm_name : Name) (before_state : Command.State) :
      CommandElabM (List (Name × Syntax)) := do
    let some id := type_stx.find? (·.isIdent) | throwError "bad type identifier"
    let results ← generalizeAux thm_stx id thm_name id.getId before_state
    return results.map (⟨·, type_stx⟩)
  -- Filter out generalizations that are not profitable. Currently only looks to avoid
  -- generalizing `AddCommGroup M` to `AddCommMonoid M` when `M` is the monoid for a module over
  -- a `Ring`.
  badGeneralization (stx type : Syntax) (replace : Name) : CommandElabM (Bool) := do
    if type.getKind != `Lean.Parser.Term.app || type[0]!.getId != `AddCommGroup ||
        replace != `AddCommMonoid then
      return false
    let groupTy := type[1]![0]!.getId
    let some declSig := stx.find? (matchNodeName `Lean.Parser.Command.declSig) | return false
    let declSigTerms := declSig.filter (matchNodeName `Lean.Parser.Term.app)
    let mod_rings := declSigTerms.filter (fun x => x[0]!.getId == `Module &&
      x[1]![1]!.getId == groupTy) |>.map (·[1]![0]!.getId)
    let semiring := declSig.find? (fun x => x[0]!.getId == `Semiring &&
      mod_rings.contains x[1]![0]!.getId)
    if let some _ := semiring then
      return false
    return true

end GeneralizeTypeClass

end Mathlib.Linter
