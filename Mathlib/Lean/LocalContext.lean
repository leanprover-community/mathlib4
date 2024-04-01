/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.LocalContext

namespace Lean.LocalContext

universe u v
variable {m : Type u → Type v} [Monad m] [Alternative m]
variable {β : Type u}

/-- Return the result of `f` on the first local declaration on which `f` succeeds. -/
@[specialize] def firstDeclM (lctx : LocalContext) (f : LocalDecl → m β) : m β :=
  do match (← lctx.findDeclM? (optional ∘ f)) with
  | none   => failure
  | some b => pure b

/-- Return the result of `f` on the last local declaration on which `f` succeeds. -/
@[specialize] def lastDeclM (lctx : LocalContext) (f : LocalDecl → m β) : m β :=
  do match (← lctx.findDeclRevM? (optional ∘ f)) with
  | none   => failure
  | some b => pure b

end Lean.LocalContext
