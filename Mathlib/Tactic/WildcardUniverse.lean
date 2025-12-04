/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

meta import Lean.Elab.App
public import Lean.Parser.Term
public import Batteries.Tactic.Lint.Misc
import Mathlib.Lean.Elab.Term

/-!
# Wildcard Universe Syntax

This module provides a convenient syntax for specifying universes, using wildcards to
automatically generate fresh universe parameters.

## Syntax

The syntax `Foo.!{u₁, u₂, ...}` allows specifying universe parameters for a constant `Foo`,
where each universe parameter can be:

- `*` : A fresh universe parameter with base name `u`
- `v*` : A fresh universe parameter with base name `v` (for any identifier `v`)
- An explicit level expression (e.g., `0`, `u+1`, `max u v`, `_` for a level mvar, etc.)

## Examples

```lean
-- Both universe parameters are fresh and inferred
#check ULift.!{*, *}

-- First parameter is a fresh universe parameter, second is inferred
#check ULift.!{*}

-- Named universe parameter
variable (C : Type*) [Category.!{v*} C]

-- Explicit universe level
variable (X : Type*) (y : ULift.!{0} X)
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
Term elaborator for the wildcard universe syntax `Foo.!{u₁, u₂, ...}`.

This elaborator handles syntax of the form `ident.!{wildcard_level,*} args*`,
where each wildcard universe can be `*`, `name*`, or an explicit level (including `_`).
-/
syntax (name := appWithWildcards)
    ident noWs ".!{" wildcard_level,+ "}" Parser.Term.argument* : term

/--
Represents the kind of wildcard universe parameter.

- `param`: A fresh universe parameter (`*` or `name*` syntax)
- `explicit`: An explicit level expression (including `_` for level mvars)
-/
inductive LevelWildcardKind where
  | param (baseName : Name := `u)
  | explicit (l : TSyntax `level)

/--
Parses an array of wildcard universe syntax into `LevelWildcardKind` values.
-/
meta def elabWildcardUniverses {m : Type → Type}
    [Monad m] [MonadExceptOf Exception m] (us : Array Syntax) :
    m (Array LevelWildcardKind) :=
  us.mapM fun u =>
    match u with
    | `(wildcard_level|*) => return .param
    | `(wildcard_level|$n:ident*) => return .param n.getId
    | `(wildcard_level|$l:level) => return .explicit l
    | _ => throwUnsupportedSyntax

/--
Extracts all universe parameter names appearing in a level expression.
-/
meta def Lean.Level.getParams (l : Level) : List Name :=
  match l with
  | .param n => [n]
  | .mvar _ => []
  | .zero => []
  | .succ l' => l'.getParams
  | .max a b => a.getParams ++ b.getParams
  | .imax a b => a.getParams ++ b.getParams

/--
Reorganizes universe parameter names to ensure proper dependency ordering.
This is used in the implementation of `elabAppWithWildcards`.
-/
meta def reorganizeUniverseParams
    (levels : Array (Option LevelWildcardKind))
    (constLevels : Array Level)
    (levelNames : List Name) : List Name := Id.run do
  let mut result := levelNames
  for ((wildcardKind, elaboratedLevel), idx) in (levels.zip constLevels).zipIdx do
    -- Only process param wildcards that elaborated to param levels
    unless wildcardKind matches some (.param _) do continue
    let .param newParamName := elaboratedLevel | continue
    -- Collect dependencies: params from later universe arguments
    let laterLevels := constLevels.toList.drop (idx + 1)
    let dependencies := laterLevels.flatMap Level.getParams |>.filter (· != newParamName)
    -- Remove newParamName from list (if it already exists)
    let currentNames := result.filter (· != newParamName)
    -- Find position after last dependency
    let lastDependencyIdx := currentNames.zipIdx
      |>.foldl (fun acc (name, idx) => if dependencies.contains name then some idx else acc) none
    let insertPos := lastDependencyIdx.map (· + 1) |>.getD 0
    result := currentNames.insertIdx insertPos newParamName
  return result

@[term_elab appWithWildcards, inherit_doc appWithWildcards]
meta def elabAppWithWildcards : TermElab := fun stx expectedType? => withoutErrToSorry do
  match stx with
  | `($id:ident.!{$us,*} $args*) =>
    let constName ← Lean.resolveGlobalConstNoOverload id
    let constInfo ← Lean.getConstInfo constName
    let numLevels := constInfo.levelParams.length

    let mut levels : Array (Option LevelWildcardKind) := (← elabWildcardUniverses us).map some
    while levels.size < numLevels do
      levels := levels.push none

    let constLevels : Array Level ← levels.mapM fun
      | none => Meta.mkFreshLevelMVar
      | some (.param baseName) => mkFreshLevelParam baseName
      | some (.explicit l) => elabLevel l

    let fn : Expr := .const constName constLevels.toList

    let (namedArgs, args, ellipsis) ← expandArgs args

    let expr ← elabAppArgs fn namedArgs args expectedType?
      (explicit := false) (ellipsis := ellipsis)

    let constLevels ← constLevels.mapM Lean.instantiateLevelMVars

    let levelNames ← getLevelNames
    let newLevelNames := reorganizeUniverseParams levels constLevels levelNames

    setLevelNames newLevelNames

    pure expr
  | _ => throwUnsupportedSyntax
