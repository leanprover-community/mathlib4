/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Lean.PrettyPrinter.Delaborator.Builtins
public import Mathlib.Init

/-!
# Notation for bundling a type into a concrete category

Concrete categories in Mathlib come with a bundling map called `of`, turning a type equipped with
the relevant typeclasses into an object of the category: `CommRingCat.of R`, `TopCat.of X`,
`ModuleCat.of R M`, ...

This file introduces the notation `↧X` for `FooCat.of X`, where the category `FooCat` is read off
from the expected type. The name `FooCat.of` is looked up in the environment rather than through a
typeclass, so `↧X` is syntactically the same as `FooCat.of`. It also provides a corresponding
delaborator `CategoryTheory.delabOf` that must be manually registered for every concrete category.


## Implementation notes

A typeclass cannot mediate this notation while keeping the elaborated term syntactically
`FooCat.of`: the typeclass assumptions of `of` vary between categories (`[CommRing R]` for
`CommRingCat`, but `[AddCommGroup M] [Module R M]` for `ModuleCat R`, etc...), so they cannot be
abstracted away. Instead, `↧` guesses the relevant `of` function from the expected type `FooCat ..`,
and in particular assumes it is named `FooCat.of`.

We further assume of `FooCat.of` that the carrier is its **last explicit argument**. This
covers both categories whose `of` is the structure constructor (`CommRingCat.of R`) and
parameterised categories, where the parameters come first (`ModuleCat.of R M`): in the latter case
the leading explicit arguments are elaborated as `_` and solved by unification with the expected
type.
-/

public meta section

namespace CategoryTheory
open Lean Elab Term Meta PrettyPrinter Delaborator SubExpr

namespace OfNotation

/-- The number of explicit arguments of a declaration of type `ty`, together with the index of the
last one among *all* of its arguments.

Metadata is ignored. Returns `none` if `ty` takes no explicit argument. -/
def explicitArgs? (ty : Expr) : Option (Nat × Nat) := go ty 0 0 none where
  /-- Walk down the binders of `ty`, where `idx` is the index of the current argument, `num` the
  number of explicit arguments seen so far and `lastIdx?` the index of the last one. -/
  go : Expr → Nat → Nat → Option Nat → Option (Nat × Nat)
    | .mdata _ ty, idx, num, lastIdx? => go ty idx num lastIdx?
    | .forallE _ _ body bi, idx, num, lastIdx? =>
      if bi.isExplicit then go body (idx + 1) (num + 1) (some idx)
      else go body (idx + 1) num lastIdx?
    | _, _, num, lastIdx? => lastIdx?.map (num, ·)

/-- Find the bundling map `FooCat.of` to use for the type `ty`, along with its number of explicit
arguments.

Before unfolding `ty`, we check its head constant `FooCat`, since a category can be reducibly
defined in terms of another one while still having its own `of`: `Profinite` reduces to
`CompHausLike _`, yet `↧X : Profinite` should be `Profinite.of X`, not `CompHausLike.of _ X`.
If no `.of` is found for the non-unfolded `ty`, we unfold it and try again. -/
partial def findOf? (ty : Expr) : MetaM (Option (Name × Nat)) := do
  let ty ← whnfCore ty
  if let .const declName _ := ty.getAppFn then
    let ofName := declName ++ `of
    -- `FooCat.of` is allowed not to exist, in which case we move on to unfolding `ty`.
    if let some info := (← getEnv).find? ofName then
      if let some (num, _) := explicitArgs? info.type then return some (ofName, num)
  match ← unfoldDefinition? ty with
  | some ty => findOf? ty
  | none => return none

end OfNotation

open OfNotation

/-- `↧X` is the object of a concrete category corresponding to the type `X`, i.e. `FooCat.of X`
where the category `FooCat` is determined by the expected type.

`↧X` elaborates to a literal application of `FooCat.of`.
* `(↧R : CommRingCat)` is `CommRingCat.of R`,
* `(↧M : ModuleCat R)` is `ModuleCat.of R M`,
* `(↧A : CommAlgCat R)` is `CommAlgCat.of R A`.

The expected type must be known. -/
syntax:max "↧" term:max : term

elab_rules : term <= expectedType
  | `(↧$x) => do
    let ty ← instantiateMVars expectedType
    if ty.getAppFn.isMVar then
      throwError "`↧` failed: the expected type must be known, but it is{indentExpr ty}"
    let some (ofName, num) ← findOf? ty |
      throwError "`↧` failed: no bundling map found for the expected type{indentExpr ty}\n\
        Expected a type whose head constant `FooCat` has an associated declaration `FooCat.of`."
    let holes ← (Array.range (num - 1)).mapM fun _ => `(_)
    elabTerm (← `($(mkCIdent ofName) $holes* $x)) expectedType

/-- Delaborate `FooCat.of … X` to `↧X`.

Tag `FooCat.of` with this to make it print using the `↧` notation:
```
@[app_delab FooCat.of] meta def FooCat.delabOf := CategoryTheory.delabOf
```
This falls back to `delabApp`, so that `FooCat.of X` doesn't get printed as `{ carrier := X, … }`
by `delabStructureInstance` even if delaboration fails in case `FooCat.of` is the constructor of
`structure FooCat`. -/
def delabOf : Delab := go <|> delabApp where
  /-- Delaborate `FooCat.of … X` to `↧X`, failing if the `↧` notation does not apply. -/
  go := whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
    let e ← getExpr
    let .const declName _ := e.getAppFn | failure
    let some (_, lastIdx) := explicitArgs? (← getConstInfo declName).type | failure
    guard <| lastIdx < e.getAppNumArgs
    withNaryArg lastIdx do `(↧$(← delab))

end CategoryTheory
