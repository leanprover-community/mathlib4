/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Thomas R. Murrills
-/
module

public import Lean.Util.CollectLevelParams
public import Lean.Elab.Term.TermElabM
public import Mathlib.Init
public import Mathlib.Lean.Elab.Term
meta import Batteries.Data.Array.Basic

/-!
# Support for `Category* C`.

In the category theory library, it is common to introduce a (universe polymorphic) general category
as follows:
```lean
universe v u
variable (C : Type u) [Category.{v} C]
```
We tend to put the universe level `v` of the morphisms ahead of the level `u` for objects
because it makes it easier to specify explicit universes when needed.

The elaborator `Category*` provides analogous behavior to `Type*` for introducing category
instances. The term elaborator `Category* C` creates a universe parameter `v`, and places it just
*before* any universe parameters appearing in `C` and its type. If `C` and its type have no
parameters, `v` becomes the last level parameter. The elaborated term is then `Category.{v} C`.

Basic usage:
```lean
variable (C : Type*) [Category* C]
```
-/

open Lean Meta Elab Term

/--
Insert `newLevel` immediately after the elements of `levelNames` which are in `us`, or at the
front of the list (as the most recent level) if there are no such elements.
-/
meta def insertAfterLevels (us : Array Name) (levelNames : List Name) (newLevel : Name) :=
  match (us.filterMap fun nm => levelNames.idxOf? nm).max? with
  | some idx => levelNames.insertIdx (idx + 1) newLevel
  | none => newLevel :: levelNames

/--
The syntax `Category* C` creates a new distinct implicit universe parameter `v`, placed
just before any parameters appearing in `C` and its type, and elaborates to `Category.{v} C`.
-/
elab "Category*" ppSpace C:term:arg : term => commitIfNoEx <| withoutErrToSorry do
  let u ← mkFreshLevelMVar
  let cExpr ← instantiateMVars <| ← elabTermEnsuringType C (some <| .sort <| .succ u)
  let tpCExpr ← instantiateMVars <| ← Meta.inferType cExpr
  let us := (collectLevelParams (collectLevelParams {} cExpr) tpCExpr).params
  let v ← mkFreshLevelParam `v (insertAfterLevels us)
  return .app (.const `CategoryTheory.Category [v, u]) cExpr
