/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/
import Lean.Exception

set_option autoImplicit true

open Lean

/--
A generalisation of `fail_if_success` to an arbitrary `MonadError`.
-/
def successIfFail [MonadError M] [Monad M] (m : M α) : M Exception := do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex

namespace Lean

namespace Exception

/--
Check if an exception is a "failed to synthesize" exception.

These exceptions are raised in several different places,
and the only commonality is the prefix of the string, so that's what we look for.
-/
def isFailedToSynthesize (e : Exception) : IO Bool := do
  pure <| (← e.toMessageData.toString).startsWith "failed to synthesize"
