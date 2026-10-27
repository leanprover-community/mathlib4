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

This linter lints against syntax of the form `foo.42`, with exceptions determined by whether the head of the type is
-/

open Lean Elab Command

namespace Mathlib.Linter

public meta section

/-- Stores type names which may be the head of terms that are allowed to use numeric projections. -/
initialize allowNumericProjExt : TagAttribute ← do
  registerTagAttribute (`allow_numeric_proj)
    "allow terms of this type to use numeric projections"
    (validate := fun n => unless (getStructureInfo? (← getEnv) n).isSome do
      throwError "Expected `{.ofConstName n}` to be a structure.")

/-- We can't add to a tag attribute later on, so hardcode the upstream exempt declarations here. -/
def upstreamAllowed := #[``Prod, ``And, ``Iff, ``Subtype, ``Fin]

/-- Lints against numeric projections such as `foo.42` unless the type's head has been registered
via `@[allow_numeric_proj]`. -/
public register_option linter.style.numericProjection : Bool := {
  defValue := false
  descr := "Lints against numeric projections such as `foo.42`."
}

/-- Whether syntax is of the form `foo.42`. -/
@[inline] def isNumericProj (stx : Lean.Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Term.proj && stx[2].isOfKind fieldIdxKind

/-- If syntax is of the form `foo.42`, returns the syntax for `42`. -/
@[inline] def numericProj? (stx : Lean.Syntax) : Option Lean.Syntax :=
  if isNumericProj stx then stx[2] else none


#check InfoTree
open Lean Meta in
@[inherit_doc linter.style.numericProjection]
def numericProjection : Linter where
  run stx := stx |> withSetOptionIn fun _ => do
    unless Linter.getLinterValue linter.style.numericProjection (← Linter.getLinterOptions) do
      return
    if (stx.find? isNumericProj).isSome then
      for t in ← getInfoTrees do
        -- Collect the warnings separately from logging them, since (compiled) `foldInfo` is faster
        -- than (interpreted, specialized) `foldInfoM`.
        let warnings := t.foldInfoTree (init := #[]) fun ctx t w => Id.run do
          if let .node (.ofTermInfo i) ch := t then
            if i.elaborator == ``Term.elabProj then
              if let some projStx := numericProj? i.stx then
                let firstInfo := ch.findSome? fun
                  | .node (.ofTermInfo i) _ => some i
                  | _ => none
                if let some i := firstInfo then
                  return w.push (i, ctx, projStx)
          return w
        for (i, ctx, stx) in warnings do
          let typeName? ← liftM <| i.runMetaM ctx do
            pure (← whnfR <|← inferType i.expr).const?
          if let some (name, _) := typeName? then
            unless upstreamAllowed.contains name || allowNumericProjExt.hasTag (← getEnv) name do
              if let some idx := stx.isFieldIdx? then
                if
                  let some fieldName := (getStructureFieldsFlattened (← getEnv) name)[idx - 1]?
                then
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
                      To exempt terms of type `{.ofConstName name}`, add `@[allow_numeric_proj]` \
                      at the declaration site of `{.ofConstName name}`."
                  continue
          -- couldn't find the const for some reason
          Linter.logLint linter.style.numericProjection stx
              m!"Numeric projections are disallowed."

initialize addLinter numericProjection


structure Foo where a : Nat
structure Bar extends Foo where b : Nat

variable (x : Bar)

#check x.1
