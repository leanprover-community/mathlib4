/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Lean.Util.CollectLevelParams
import Lean.Elab.Term.TermElabM
import Batteries.Data.Array.Basic
import Mathlib.Init

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
parameters, `v` is becomes the last level parameter. The elaborated term is then `Category.{v} C`.

Basic usage:
```lean
variable (C : Type*) [Category* C]
```
-/

open Lean Meta Elab Term

/--
The syntax `Category* C` creates a new distinct implicit universe parameter `v`, placed
just before any parameters appearing in `C` and its type, and elaborates to `Category.{v} C`.
-/
elab "Category*" ppSpace C:term : term => commitIfNoEx <| withoutErrToSorry do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let cExpr ← instantiateMVars <| ← elabTermEnsuringType C (some <| .sort <| .succ u)
  let tpCExpr ← instantiateMVars <| ← Meta.inferType cExpr
  let cat := .const `CategoryTheory.Category [v, u]
  let levelNames ← getLevelNames
  let ⟨mctx, vs, _, out⟩ :=
    (← getMCtx).levelMVarToParam (fun n => levelNames.elem n) (· != v.mvarId!) cat `v 1
  let [v] := vs.toList
    | throwError "Unexpected Error:{indentD out}\ndoesn't have exactly one new level parameter"
  let us := (collectLevelParams {} cExpr).params ++ (collectLevelParams {} tpCExpr).params
  setLevelNames <| match (us.filterMap fun nm => levelNames.findIdx? (· == nm)).max? with
  | some idx => levelNames.insertIdx (idx + 1) v
  | none => v :: levelNames
  setMCtx mctx
  return .app out cExpr
