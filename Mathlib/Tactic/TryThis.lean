/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean

/-!
# 'Try this' tactic macro

This is a convenient shorthand intended for macro authors to be able to generate "Try this"
recommendations. (It is not the main implementation of 'Try this',
which is implemented in Lean core, see `Lean.Meta.Tactic.TryThis`.)
-/

namespace Mathlib.Tactic
open Lean

/-- Produces the text `Try this: <tac>` with the given tactic, and then executes it. -/
elab tk:"try_this" tac:tactic : tactic => do
  Elab.Tactic.evalTactic tac
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)

/-- Produces the text `Try this: <tac>` with the given conv tactic, and then executes it. -/
elab tk:"try_this" tac:conv : conv => do
  Elab.Tactic.evalTactic tac
  Meta.Tactic.TryThis.addSuggestion tk tac (origSpan? := ← getRef)
