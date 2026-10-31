/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

import Lean.Parser.Term
import Batteries.Tactic.Lint.Misc

public meta import Lean.Elab.App
public import Mathlib.Lean.Elab.Term

/-!
# Wildcard Universe Syntax

This module provides a convenient syntax for specifying universes, using wildcards to
automatically generate fresh universe parameters.

## Syntax

This overrides Lean's syntax `Foo.{u₁, u₂, ...}` to enable wildcards when specifying universe
parameters for a constant `Foo`. Each parameter can now be:
- `*` : A fresh universe parameter with base name `u`
- `v*` : A fresh universe parameter with base name `v` (for any identifier `v`)
- An explicit level expression (e.g., `0`, `u+1`, `max u v`, `_` for a level mvar, etc.)

## Examples

```lean
-- Both universe parameters are fresh and inferred
#check ULift.{*, *}

-- First parameter is a fresh universe parameter, second is inferred
#check ULift.{*}

-- Named universe parameter
variable (C : Type*) [Category.{v*} C]

-- Explicit universe level
variable (X : Type*) (y : ULift.{0} X)
```

## Implementation Notes

The elaborator automatically reorganizes universe parameters to ensure the ordering matches what
is indicated by the syntax.

## Projects

- Add support for nested wildcard levels, e.g. `Category.{* + 1}`.
-/

open Lean Meta Elab Term

/-- The syntax category for wildcard universe levels -/
declare_syntax_cat wildcard_level
/-- The syntax category for comma-separated wildcard universe levels.
We need this as a separate category to handle the token `,*` as separate `,` and `*`. -/
declare_syntax_cat comma_wildcard_level

@[nolint docBlame] syntax "*" : wildcard_level
@[nolint docBlame] syntax ident noWs "*" : wildcard_level
@[nolint docBlame] syntax level : wildcard_level

@[nolint docBlame] syntax ",*" : comma_wildcard_level
@[nolint docBlame] syntax ", " wildcard_level : comma_wildcard_level

/--
Term elaborator for the wildcard universe syntax `Foo.{u₁, u₂, ...}`.

This elaborator handles syntax of the form `ident.{wildcard_level,+} args*`,
where each wildcard universe can be `*`, `name*`, or an explicit level (including `_`).
-/
syntax:arg (name := appWithWildcards)
    ("@" noWs)? ident noWs ".{" wildcard_level comma_wildcard_level* "}"
      Parser.Term.argument* : term

/--
Represents the kind of wildcard universe parameter.

- `param`: A fresh universe parameter (`*` or `name*` syntax)
- `explicit`: An explicit level expression (including `_` for level mvars)
-/
inductive LevelWildcardKind where
  | param (baseName : Name)
  | explicit (l : TSyntax `level)
  | mvar

meta section

/--
Extracts the base name from a universe parameter name.
For example, `u_1` becomes `u`, `v_2` becomes `v`, and `w` stays `w`.
-/
def getBaseName (n : Name) : Name :=
  let s := n.toString
  let basePart := s.takeWhile (· != '_')
  basePart.toName

/--
A helper function to convert an array of `comma_wildcard_level`s into
an array of `wildcard_level`s.
-/
def mkWildcardLevelStx {m : Type → Type} [Monad m] [MonadExceptOf Exception m] [MonadQuotation m]
    (us : Array (TSyntax `comma_wildcard_level)) :
    m (Array (TSyntax `wildcard_level)) :=
  us.mapM fun u => do
    match u with
    | `(comma_wildcard_level|,*) => `(wildcard_level|*)
    | `(comma_wildcard_level|, $u:wildcard_level) => `(wildcard_level|$u)
    | _ => throwUnsupportedSyntax

/--
Parses an array of wildcard universe syntax into `LevelWildcardKind` values.
Takes the constant's level parameter names to use as defaults for `*` wildcards.
-/
def elabWildcardUniverses {m : Type → Type} [Monad m] [MonadExceptOf Exception m]
    (us : Array Syntax) (constLevelParams : List Name) :
    m (Array LevelWildcardKind) :=
  us.mapIdxM fun idx u =>
    match u with
    | `(wildcard_level|*) =>
        let baseName := (constLevelParams[idx]?.map getBaseName).getD `u
        return .param baseName
    | `(wildcard_level|$n:ident*) => return .param n.getId
    | `(wildcard_level|$l:level) => return .explicit l
    | _ => throwUnsupportedSyntax

/--
Reorganizes universe parameter names to ensure proper dependency ordering.

Algorithm:
* Iterate over universe arguments from left to right.
* Only act on arguments that were written as a wildcard parameter (`*` or `name*`).
* For such a parameter name `p` at index `i`, compute `dependencies` as the set of
  level parameter names appearing in the *later* universe arguments
  `constLevels[i+1..]` (excluding `p` itself).
* Remove `p` from the current list, then insert it immediately after
  the last occurrence of any name in `dependencies`. If no dependency occurs in
  the list, insert `p` at the front.

This only reorders parameter names introduced by wildcards; explicit levels and
level mvars are ignored. The result keeps any parameters used by later arguments
before the freshly introduced wildcard parameter, which matches the dependency
ordering implied by the application.

This is used in the implementation of `elabAppWithWildcards`.
-/
def reorganizeUniverseParams
    (levels : Array LevelWildcardKind)
    (constLevels : Array Level)
    (levelNames : List Name) : List Name := Id.run do
  let mut result := levelNames
  for wildcardKind in levels, elaboratedLevel in constLevels, idx in 0...* do
    -- Only process param wildcards that elaborated to param levels
    unless wildcardKind matches .param _ do continue
    let .param newParamName := elaboratedLevel | continue
    -- Collect dependencies: params from later universe arguments
    let dependencies :=
      constLevels.foldr (stop := idx + 1) CollectLevelParams.visitLevel {} |>.params
    -- Remove newParamName from list
    let currentNames := result.erase newParamName
    -- Find position after last dependency
    let insertPos := currentNames.zipIdx
      |>.findRev? (fun (name, _) => dependencies.contains name)
      |>.map (·.snd + 1) |>.getD 0
    result := currentNames.insertIdx insertPos newParamName
  return result

@[term_elab appWithWildcards, inherit_doc appWithWildcards]
public def elabAppWithWildcards : TermElab := fun stx expectedType? => withoutErrToSorry do
  match stx with
  | `($[@%$expl]?$id:ident.{$u $us*} $args*) =>
    -- Check for local variables which shouldn't have explicit universe parameters
    if let some (e, _) ← resolveLocalName id.getId then
      throwError "invalid use of explicit universe parameters, `{e}` is a local variable"

    -- Resolve constant name
    let constName ← realizeGlobalConstNoOverloadWithInfo id
    let constInfo ← getConstInfo constName

    -- Parse and elaborate wildcard universes
    let us : Array Syntax := #[u] ++ (← mkWildcardLevelStx us)
    let mut levels : Array LevelWildcardKind ← elabWildcardUniverses us constInfo.levelParams
    while levels.size < constInfo.levelParams.length do
      levels := levels.push .mvar

    let constLevels : Array Level ← levels.mapM fun
      | .mvar => mkFreshLevelMVar
      | .param baseName => mkFreshLevelParam baseName
      | .explicit l => elabLevel l

    -- Create constant expression using Term.mkConst (handles deprecation)
    let fn ← Term.mkConst constName constLevels.toList

    -- Elaborate arguments
    let (namedArgs, args, ellipsis) ← expandArgs args
    let expr ← elabAppArgs fn namedArgs args expectedType?
      (explicit := expl.isSome) (ellipsis := ellipsis)

    -- Instantiate level mvars and reorganize
    let constLevels ← constLevels.mapM instantiateLevelMVars
    setLevelNames <| reorganizeUniverseParams levels constLevels (← getLevelNames)

    return expr

  | _ => throwUnsupportedSyntax

end
