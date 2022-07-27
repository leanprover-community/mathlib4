/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers
-/
import Lean
open Lean

/--
A generalisation of `fail_if_success` to an arbitrary `MonadError`.
-/
def successIfFail [MonadError M] [Monad M] (m : M α) : M Exception := do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex
