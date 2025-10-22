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
*before* any universe parameters appearing in `C`. If `C` has no parameters, `v` is becomes the
last level parameter. The elaborated term is then `Category.{v} C`.

Basic usage:
```lean
variable (C : Type*) [Category* C]
```
-/

open Lean Meta Elab Term
open CategoryTheory

/--
The syntax `Category* C` creates a new distinct implicit universe parameter `v`, placed
just before any parameters appearing in `C`, and elaborates to `Category.{v} C`.
-/
elab "Category*" ppSpace C:term : term => do
  let u ← mkFreshLevelMVar
  let v ← mkFreshLevelMVar
  let C ← instantiateExprMVars <| ← elabTermEnsuringType C (some <| .sort <| .succ u)
  let instTp := .app (.const ``Category [v,u]) C
  let levelNames ← getLevelNames
  let ⟨mctx, vs, _, out⟩ :=
    (← getMCtx).levelMVarToParam (fun n => levelNames.elem n) (fun _ => false) instTp `v 1
  let v::[] := vs.toList | throwError "The term{indentD C}\nhas level mvars"
  let us := (collectLevelParams {} C).params
  match (us.filterMap fun nm => levelNames.findIdx? fun x => x == nm).max? with
  | some idx => setLevelNames <| levelNames.insertIdx (idx + 1) v
  | none => setLevelNames <| v :: levelNames
  setMCtx mctx
  return out
