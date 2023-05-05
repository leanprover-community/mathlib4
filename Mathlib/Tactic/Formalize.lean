/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import LLM.FindChatBot

/-!
# `#formalize` command, requesting auto-formalization via a large language model.

You must have a large language model available for this to work.

Recommended is to use an OpenAI API key, with available quota,
stored in the environment variables `OPENAI_API_KEY` for this to work.
We start by trying the "gpt-4" model, but if this is not available we fall back automatically to
"gpt-3.5-turbo".

If you don't have access to GPT, or don't want to use it, it is also possible
to use local LLMs. Running #formalize will fail, but print instructions for
setting one up.
-/

open LLM GPT

/-- The system message for `#formalize`. -/
-- Please feel free to suggest changes, or to provide a customization hook.
-- Not much thought has gone into this prompt!
def systemMessage : String :=
"You are an expert mathematician user of the interactive theorem prover Lean 4.
You will be ask to formalize mathematical statements into Lean 4.

Your answer should be in the form of a Lean 4 theorem statement
equivalent to the query statement, with the proof given as `sorry`.
You may include a short natural language explanation as a doc-string.

Here are some examples:
"

/--
A list of examples for few-shot prompting.
-/
def examples : List (String × String) :=
[
("There are infinitely many prime numbers.",
"theorem infinitely_many_primes : ∀ N : Nat, ∃ p, N < p ∧ p.Prime := sorry"),
("The length of the concatenation of two lists is the sum of the lengths of the lists.",
"theorem List.append_length {L M : List α} : (L ++ M).length = L.length + M.length := sorry"),
("The Lebesgue number lemma.",
"/-- Let `c : ι → Set α` be an open cover of a compact set `s`. Then there exists an entourage
`n` such that for each `x ∈ s` its `n`-neighborhood is contained in some `c i`. -/
theorem lebesgue_number_lemma {α : Type u} [UniformSpace α] {s : Set α} {ι} {c : ι → Set α}
    (hs : IsCompact s) (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
    ∃ n ∈ 𝓤 α, ∀ x ∈ s, ∃ i, { y | (x, y) ∈ n } ⊆ c i := sorry")]

/--
Construct the list of messages of the system message and the examples.
-/
def history : List Message :=
⟨.system, systemMessage⟩ :: examples.bind fun (prompt, response) =>
  [⟨.user, prompt⟩, ⟨.assistant, response⟩]

open Lean Elab Command

elab tk:"#formalize" t:term : command => liftTermElabM do
  let .lit (.strVal s) ← Term.elabTerm t none
    | throwError "#formalize must be followed by a string literal"
  if s.trim.endsWith "." || s.trim.endsWith "?" then
    logInfoAt tk (← (← findChatBot).sendMessages (history ++ [⟨.user, s⟩]))
  else logInfoAt tk <|
    "Please terminate your request with a '.' or '?', to avoid intermediate requests to the LLM."
