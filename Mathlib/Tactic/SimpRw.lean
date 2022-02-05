/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Mario Carneiro
-/

import Lean

namespace Mathlib.Tactic

open Lean Parser.Tactic

/--
`simp_rw` functions as a mix of `simp` and `rw`. Like `rw`, it applies each
rewrite rule in the given order, but like `simp` it repeatedly applies these
rules and also under binders like `∀ x, ...`, `∃ x, ...` and `λ x, ...`.
Usage:

- `simp_rw [lemma_1, ..., lemma_n]` will rewrite the goal by applying the
  lemmas in that order. A lemma preceded by `←` is applied in the reverse direction.
- `simp_rw [lemma_1, ..., lemma_n] at h₁ ... hₙ` will rewrite the given hypotheses.
- `simp_rw [...] at *` rewrites in the whole context: all hypotheses and the goal.

Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.
For example, neither `simp` nor `rw` can solve the following, but `simp_rw` can:

```lean
example {a : ℕ}
  (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
  (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
  (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 :=
by simp_rw [h1, h2]
```
-/
macro "simp_rw " rws:rwRuleSeq loc:(ppSpace location)? : tactic => do
  let loc := loc.getOptional?
  let stx ← rws[1].getSepArgs.mapM fun
    | `(rwRule| $e:term) => `(tactic| simp%$e only [$e:term] $(loc)?)
    | `(rwRule| ←%$tk $e:term) => `(tactic| simp%$tk only [← $e:term] $(loc)?)
    | _ => Macro.throwUnsupported
  `(tactic| ($[$stx]*))
