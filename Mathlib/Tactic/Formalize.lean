/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Util.GPT.Chat

/-!
# `#formalize` command, requesting auto-formalization from GPT.

You must have your OpenAI API key, with available quota,
stored in the environment variables `OPENAI_API_KEY` for this to work.
We start by trying the "gpt-4" model, but if this is not available we fall back automatically to
"gpt-3.5-turbo".
-/

open Lean Elab Command

/-- The system message for `#formalize`. -/
-- Please feel free to suggest changes, or to provide a customization hook.
-- Not much thought has gone into this prompt!
def systemMessage : String :=
"You are an expert mathematician user of the interactive theorem prover Lean 4.
You will be ask to formalize mathematical statements into Lean 4.

Here are some examples:

Query: There are infinitely many prime numbers.
Response:
theorem infinitely_many_primes : ∀ N : Nat, ∃ p, N < p ∧ p.Prime := sorry

Query: The length of the concatenation of two lists is the sum of the lengths of the lists.
theorem List.append_length {L M : List α} : (L ++ M).length = L.length + M.length := sorry

Query: The Lebesgue number lemma.
Response:
/-- Let `c : ι → Set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {α : Type u} [UniformSpace α] {s : Set α} {ι} {c : ι → Set α}
    (hs : IsCompact s) (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ i, { y | (x, y) ∈ n } ⊆ c i := sorry

Your answer should be in the form of a Lean 4 theorem statement equivalent to the query statement,
with the proof given as `sorry`.
You may include a short natural language explanation as a doc-string.
"

elab tk:"#formalize" t:term : command => liftTermElabM do
  let .lit (.strVal s) ← Term.elabTerm t none
    | throwError "#formalize must be followed by a string literal"
  if s.trim.endsWith "." || s.trim.endsWith "?" then
    logInfoAt tk (← GPT.send s systemMessage)
  else logInfoAt tk <|
    "Please terminate your request with a '.' or '?', to avoid intermediate requests to GPT."
