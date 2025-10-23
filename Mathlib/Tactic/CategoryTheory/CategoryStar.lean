/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Category.Basic

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

Note: `Category* C` expects both `C` and its type to *not involve* any level mvars.
-/

open Lean Meta Elab Term
open CategoryTheory

/--
The syntax `Category* C` creates a new distinct implicit universe parameter `v`, placed
just before any parameters appearing in `C` and its type, and elaborates to `Category.{v} C`.
-/
elab "Category*" ppSpace C:term : term => commitIfNoEx <| withoutErrToSorry do
  let u ← mkFreshLevelMVar
  let cExpr ← instantiateExprMVars <| ← elabTermEnsuringType C (some <| .sort <| .succ u)
  if cExpr.hasLevelMVar then
    throwError "The term{indentD cExpr}\nhas level mvars"
  let tpCExpr ← instantiateExprMVars <| ← Meta.inferType cExpr
  if tpCExpr.hasLevelMVar then
    throwError "The type{indentD tpCExpr}\nof{indentD cExpr}\nhas level mvars"
  let instTp ← instantiateMVars <| .app (.const ``Category [← mkFreshLevelMVar, u]) cExpr
  let levelNames ← getLevelNames
  -- We must ensure that `u` is still uninstantiated at this point, otherwise the next
  -- line will panic.
  unless u.isMVar do
    throwError "Unexpected Error:{u} is not a level mvar."
  let ⟨mctx, vs, _, out⟩ :=
    (← getMCtx).levelMVarToParam (fun n => levelNames.elem n)
    (fun id => id == u.mvarId!) instTp `v 1
  let v::[] := vs.toList
    | throwError "Unexpected Error:{indentD out}\ndoesn't have exactly one new level parameter"
  let us := (collectLevelParams {} cExpr).params ++ (collectLevelParams {} tpCExpr).params
  match (us.filterMap fun nm => levelNames.findIdx? fun x => x == nm).max? with
  | some idx => setLevelNames <| levelNames.insertIdx (idx + 1) v
  | none => setLevelNames <| v :: levelNames
  setMCtx mctx
  return out
