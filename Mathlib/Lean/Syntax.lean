/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Mathlib.Init

/-!
# Addional utilities for `Syntax`
-/

namespace Lean.Syntax

/-- Finds the first subtree of `stx` for which `p subtree` is `some a`, descending the tree from
the top. -/
partial def findSome? {α} (p : Syntax → Option α) : Syntax → Option α
  | stx@(.node _ _ args) => p stx <|> args.findSome? (findSome? p)
  | stx                  => p stx

/-- Returns `true` exactly when `stxᵢ.getRange? canonicalOnlyᵢ` are both `some _` and are equal.
This means that `rangeEq` returns `false` if either arguments have no position information. -/
def rangeEq (stx₁ stx₂ : Syntax) (canonicalOnly₁ canonicalOnly₂ := true) : Bool :=
  match stx₁.getRange? canonicalOnly₁, stx₂.getRange? canonicalOnly₂ with
  | some r₁, some r₂ => r₁ == r₂
  | _, _ => false

end Lean.Syntax
