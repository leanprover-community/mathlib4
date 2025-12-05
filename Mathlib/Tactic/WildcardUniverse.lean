/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Lean.Parser.Term
public import Batteries.Tactic.Lint.Misc

meta import Lean.Elab.App
import Mathlib.Lean.Elab.Term

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
-/

open Lean Elab Term

declare_syntax_cat wildcard_level

@[nolint docBlame] syntax "*" : wildcard_level
@[nolint docBlame] syntax ident noWs "*" : wildcard_level
@[nolint docBlame] syntax level : wildcard_level

/--
Term elaborator for the wildcard universe syntax `Foo.{u₁, u₂, ...}`.

This elaborator handles syntax of the form `ident.{wildcard_level,*} args*`,
where each wildcard universe can be `*`, `name*`, or an explicit level (including `_`).
-/
syntax (name := appWithWildcards)
    ("@" noWs)? ident noWs ".{" wildcard_level,+ "}" Parser.Term.argument* : term

/--
Represents the kind of wildcard universe parameter.

- `param`: A fresh universe parameter (`*` or `name*` syntax)
- `explicit`: An explicit level expression (including `_` for level mvars)
-/
inductive LevelWildcardKind where
  | param (baseName : Name)
  | explicit (l : TSyntax `level)

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
Parses an array of wildcard universe syntax into `LevelWildcardKind` values.
Takes the constant's level parameter names to use as defaults for `*` wildcards.
-/
def elabWildcardUniverses {m : Type → Type}
    [Monad m] [MonadExceptOf Exception m] (us : Array Syntax) (constLevelParams : List Name) :
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
Extracts all universe parameter names appearing in a level expression.
-/
def Lean.Level.getParams (l : Level) : Array Name :=
  (Lean.CollectLevelParams.visitLevel l {}).params

/--
Reorganizes universe parameter names to ensure proper dependency ordering.
This is used in the implementation of `elabAppWithWildcards`.
-/
def reorganizeUniverseParams
    (levels : Array (Option LevelWildcardKind))
    (constLevels : Array Level)
    (levelNames : List Name) : List Name := Id.run do
  let mut result := levelNames
  for ((wildcardKind, elaboratedLevel), idx) in (levels.zip constLevels).zipIdx do
    -- Only process param wildcards that elaborated to param levels
    unless wildcardKind matches some (.param _) do continue
    let .param newParamName := elaboratedLevel | continue
    -- Collect dependencies: params from later universe arguments
    let laterLevels := constLevels.extract (idx + 1) constLevels.size
    let dependencies := laterLevels.flatMap (·.getParams) |>.filter (· != newParamName)
    -- Remove newParamName from list (if it already exists)
    let currentNames := result.filter (· != newParamName)
    -- Find position after last dependency
    let lastDependencyIdx := currentNames.zipIdx
      |>.foldl (fun acc (name, idx) => if dependencies.contains name then some idx else acc) none
    let insertPos := lastDependencyIdx.map (· + 1) |>.getD 0
    result := currentNames.insertIdx insertPos newParamName
  return result

@[term_elab appWithWildcards, inherit_doc appWithWildcards]
def elabAppWithWildcards : TermElab := fun stx expectedType? => withoutErrToSorry do
  match stx with
  | `($[@%$expl]?$id:ident.{$us,*} $args*) =>
    let constName ← Lean.resolveGlobalConstNoOverload id
    let constInfo ← Lean.getConstInfo constName
    let numLevels := constInfo.levelParams.length

    let mut levels : Array (Option LevelWildcardKind) :=
      (← elabWildcardUniverses us constInfo.levelParams).map some
    while levels.size < numLevels do
      levels := levels.push none

    let constLevels : Array Level ← levels.mapM fun
      | none => Meta.mkFreshLevelMVar
      | some (.param baseName) => mkFreshLevelParam baseName
      | some (.explicit l) => elabLevel l

    let fn : Expr ← mkConst constName constLevels.toList

    let (namedArgs, args, ellipsis) ← expandArgs args

    let expr ← elabAppArgs fn namedArgs args expectedType?
      (explicit := expl.isSome) (ellipsis := ellipsis)

    let constLevels ← constLevels.mapM Lean.instantiateLevelMVars

    let levelNames ← getLevelNames
    let newLevelNames := reorganizeUniverseParams levels constLevels levelNames

    setLevelNames newLevelNames

    return expr

  | _ => throwUnsupportedSyntax

end
