/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Lean

namespace Lean

namespace Expr

open Lean.Meta

/-- `getBinderName e` returns `some n` if `e` is an expression of the form `∀ n, ...`
and `none` otherwise. -/
def getBinderName (e : Expr) : MetaM (Option Name) := do
  match ← withReducible (whnf e) with
  | .forallE (binderName := n) .. | .lam (binderName := n) .. => pure (some n)
  | _ => pure none
