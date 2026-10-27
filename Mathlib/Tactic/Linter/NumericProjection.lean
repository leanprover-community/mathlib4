/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.InfoTree.Util
public meta import Lean.Meta.Tactic.TryThis
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

import Lean.Elab.App

/-!
# Linting against numeric projections

This linter lints against syntax of the form `foo.42`, with exceptions determined by whether the head of the type is either in a hardcoded exemptions list (if upstream) or tagged with
`@[allow_numeric_proj]`.

## TODO

- Should we necessarily see through type defs? Maybe we should insist that the typedefs themselves
  are tagged instead.
-/

open Lean Elab Command

namespace Mathlib.Linter

public meta section

/-- Stores type names which may be the head of terms that are allowed to use numeric projections. -/
initialize allowNumericProjExt : TagAttribute ← do
  registerTagAttribute (`allow_numeric_proj)
    "Allow terms of this type to use numeric projections."
    (validate := fun n => unless (getStructureInfo? (← getEnv) n).isSome do
      throwError "Expected `{.ofConstName n}` to be a structure.")

/-- We can't add to a tag attribute later on, so hardcode the upstream exempt declarations here. -/
def upstreamAllowed := #[``Prod, ``PProd, ``Sigma, ``PSigma, ``And, ``Iff, ``Subtype, ``Fin]

/-- Lints against numeric projections such as `foo.42` unless the type's head has been registered
via `@[allow_numeric_proj]`. -/
public register_option linter.style.numericProjection : Bool := {
  defValue := false
  descr := "Lints against numeric projections such as `foo.42`."
}

-- TODO: rewrite
/-- If `stx` is the `identProj`-wrapped field index of a numeric projection which the elaborator
resolved to the projection function `projFn`, returns the field index syntax and `projFn`.

The elaborator records this info for every numeric projection on a `structure`, including ones not
elaborated by `elabProj` (e.g. `f.1 x` and the inner projection of `x.1.2`). Since the structure has
already been found by reducing the type, we don't need to reduce it again. -/
@[inline] def numericProjFn? (i : Elab.TermInfo) : Option (Lean.Syntax × Name) := do
  guard <| i.stx.isOfKind Parser.Term.identProjKind
  let idxStx := i.stx[0]
  guard <| idxStx.isOfKind fieldIdxKind
  -- Note: we do not need to worry about metavariables and mdata/annotations here, because
  -- the info nodes in question are always created through `addProjTermInfo` and `Term.mkConst`.
  -- If core changes and tests break, though, consider `.cleanupAnnotations` and/or
  -- `i.runMetaM ctx (instantiateMVars i.expr)`.
  return (idxStx, ← i.expr.constName?)

open Meta in
@[inherit_doc linter.style.numericProjection]
def numericProjection : Linter where
  run stx := stx |> withSetOptionIn fun _ => do
    unless Linter.getLinterValue linter.style.numericProjection (← Linter.getLinterOptions) do
      return
    if (stx.find? (·.isOfKind fieldIdxKind)).isSome then
      for t in ← getInfoTrees do
        -- Collect the warnings separately from logging them, since (compiled) `foldInfo` is faster
        -- than (interpreted, specialized) `foldInfoM`.
        let warnings := t.foldInfo (init := #[]) fun _ info w => Id.run do
          if let .ofTermInfo i := info then
            if let some proj := numericProjFn? i then
              return w.push proj
          return w
        unless warnings.isEmpty do
          -- Deduplicate by range; likely only a small number of warnings, so an `Array` is fast
          let mut ranges := Array.emptyWithCapacity warnings.size
          for (stx, projFn) in warnings do
            if let some range := stx.getRange? (canonicalOnly := true) then
              if ranges.contains range then continue else ranges := ranges.push range
            else continue
            let env ← getEnv
            let some { ctorName, i, .. } := env.getProjectionFnInfo? projFn | continue
            let some (.ctorInfo { induct := structName, .. }) := env.find? ctorName | continue
            if upstreamAllowed.contains structName || allowNumericProjExt.hasTag env structName then
              continue
            let some fieldName := (getStructureInfo? env structName).bind (·.fieldNames[i]?)
              | continue
            let msg ← liftCoreM <|
              Hint.mkSuggestionsMessage
                #[{
                  suggestion := toString fieldName,
                  preInfo? := "Instead, use `.",
                  postInfo? := "`.", diffGranularity := .none }]
                stx none false
            Linter.logLint linter.style.numericProjection stx
              m!"Numeric projections are disallowed.\n\
                {msg}\n\n\
                To exempt terms of type `{.ofConstName structName}`, add \
                `@[allow_numeric_proj]` at the declaration site of `{.ofConstName structName}`."

initialize addLinter numericProjection
