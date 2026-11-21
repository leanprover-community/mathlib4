/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Meta.Tactic.TryThis
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Linting against numeric projections

This linter lints against numeric projections in syntax, i.e. syntax of the form `foo.2`, and
suggests replacing it with the corresponding field name projection.

Structures tagged with `@[allow_numeric_proj]` are exempt from this linter, as are structures from
upstream that are hardcoded into the linter (since tag attributes do not allow tagging declarations
downstream).

## TODO

- Should we necessarily see through type defs? Maybe we should insist that the typedefs themselves
  are tagged instead.
-/

open Lean Elab Command

namespace Mathlib.Linter

meta section

/-- Structures `Foo` tagged with `@[allow_numeric_proj]` are exempt from the `numericProjections`
linter, and thus their projections are allowed to appear as numeric projections in syntax. E.g., if
`foo : Foo`, the linter will not warn on `foo.2`. -/
public initialize allowNumericProjExt : TagAttribute ←
  registerTagAttribute `allow_numeric_proj
    "Allow numeric projections of the tagged structure type to appear in syntax."
    (validate := fun n => unless isStructure (← getEnv) n do
      throwError "Expected `{.ofConstName n}` to be a structure.")

/-- We can't add to a tag attribute later on, so hardcode the upstream exempt declarations here. -/
@[inline]
def upstreamAllowed := #[``Prod, ``PProd, ``Sigma, ``PSigma, ``And, ``Iff]

/-- Whether a term whose type has a head of `structName` is allowed to use numeric projections. -/
@[inline] public def allowsNumericProj (env : Environment) (structName : Name) :=
  upstreamAllowed.contains structName || allowNumericProjExt.hasTag env structName

/-- Lints against numeric structure projections such as `foo.2`, unless the projection acts on a
structure which has been registered as exempt from this linter via `@[allow_numeric_proj]`. -/
public register_option linter.style.numericProjections : Bool := {
  defValue := false
  descr := "Lints against numeric structure projections such as `foo.2`."
}

/--
When Lean elaborates projection syntax and associates an info node with the projection, Lean
creates synthetic syntax for that info (which is not present in the original parsed syntax) with
"faked" syntax nodekind `identProjKind`. `numericProjFn?` detects infos created in this way which
additionally use a number instead of a field name (`fieldIdx`) and returns the projection syntax
along with the projection function's constant name (which is recorded in the info's `expr`).

Note that the projection name from the `expr` is guaranteed to be the projection function Lean has
actually found for the projection syntax being used.

Note also that not every projection goes through the `elabProj` elaborator which is responsible for
elaborating projection syntax like `a.1`. In particular, syntax including: `a.1 x` (surprisingly),
the inner `a.1` in `a.1.2`, `@a.1`, `a |>.1`, and so on all do not record the `elabProj` elaborator
as responsible for their elaboration in the infotrees. As such, we do not gate on this.
-/
@[inline] def numericProjFn? (i : TermInfo) : Option (Lean.Syntax × Name) := do
  guard <| i.stx.isOfKind Parser.Term.identProjKind
  let idxStx := i.stx[0]
  guard <| idxStx.isOfKind fieldIdxKind
  -- Note: we do not need to worry about metavariables and mdata/annotations here, because
  -- the info nodes in question are always created through `addProjTermInfo` and `Term.mkConst`.
  -- If core changes and tests break, though, consider `.cleanupAnnotations` and/or
  -- `i.runMetaM ctx (instantiateMVars i.expr)`.
  return (idxStx, ← i.expr.constName?)

/-- Returns `some (structName, fieldName)` if `projFn` is a structure projection that is not
allowed to have been created by numeric projection syntax, consulting `allowsNumericProj`. -/
@[inline] def disallowedNumericProjFn? (env : Environment) (projFn : Name) :
    Option (Name × Name) := do
  -- Note: we silently return `none` if these fail, since the numeric projection may be for a
  -- one-constructor inductive (which has no fields to suggest replacing it with).
  let { ctorName, i, .. } ← env.getProjectionFnInfo? projFn
  let .ctorInfo { induct := structName, .. } ← env.find? ctorName | none
  guard !(allowsNumericProj env structName)
  let fieldName ← (getStructureInfo? env structName).bind (·.fieldNames[i]?)
  some (structName, fieldName)

open Meta in
@[inherit_doc linter.style.numericProjections]
def numericProjections : Linter where
  run stx := stx |> withSetOptionIn fun _ => do
    unless Linter.getLinterValue linter.style.numericProjections (← Linter.getLinterOptions) do
      return
    if stx.find? (·.isOfKind fieldIdxKind) |>.isSome then
      -- Collect the warnings separately from logging them, since (compiled) `foldInfo` is faster
      -- than (interpreted, specialized) `foldInfoM`.
      let warnings := (← getInfoTrees).foldl (init := #[]) fun w t =>
        t.foldInfo (init := w) fun ctx info w => Id.run do
          if let .ofTermInfo i := info then
            if let some (idStx, projFn) := numericProjFn? i then
              if let some structAndField := disallowedNumericProjFn? ctx.env projFn then
                return w.push (idStx, structAndField)
          return w
      unless warnings.isEmpty do
        -- Deduplicate by range; likely only a small number of potential warnings, so a linear
        -- `Array.contains` check is fast
        let mut loggedRanges := Array.emptyWithCapacity warnings.size
        for (stx, structName, fieldName) in warnings do
          let some range := stx.getRange? (canonicalOnly := true) | continue
          if loggedRanges.contains range then continue
          loggedRanges := loggedRanges.push range
          let msg ← liftCoreM <|
            Hint.mkSuggestionsMessage (ref := stx)
              (codeActionPrefix? := none) (forceList := false)
              #[{
                preInfo? := "Instead, use `.",
                suggestion := toString fieldName,
                postInfo? := "`.",
                diffGranularity := .none
              }]
          Linter.logLint linter.style.numericProjections stx m!"\
            Numeric projections are disallowed.\n\
            {msg}\n\n\
            To allow numeric projections for all terms of type `{.ofConstName structName}`, add \
            `@[allow_numeric_proj]` at the declaration site of `{.ofConstName structName}`."

initialize addLinter numericProjections
