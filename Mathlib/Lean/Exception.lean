import Lean
open Lean

def successIfFail [MonadError M] [Monad M] (m : M α) : M Exception := do
  match ← tryCatch (m *> pure none) (pure ∘ some) with
  | none => throwError "Expected an exception."
  | some ex => return ex
