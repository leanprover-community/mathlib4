/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Mario Carneiro, Alex J. Best
-/
module

public import Mathlib.Init

/-!
# The `simp_rw` tactic

This file defines the `simp_rw` tactic: it functions as a mix of `simp` and `rw`.
Like `rw`, it applies each rewrite rule in the given order, but like `simp` it repeatedly applies
these rules and also under binders like `∀ x, ...`, `∃ x, ...` and `fun x ↦ ...`.
-/

public meta section
namespace Mathlib.Tactic

open Lean Elab.Tactic
open Parser.Tactic (optConfig rwRuleSeq location getConfigItems)

/-- A version of `withRWRulesSeq` (in core) that doesn't attempt to find equation lemmas, and simply
passes the rw rules on to `x`.

In this case, `x` passes the rules to `simp only`, and `simp only` already finds the equation
lemmas, so we don't need to do that here.
-/
def withSimpRWRulesSeq (rwRulesSeqStx : Syntax)
    (x : (symm : Bool) → (term : Syntax) → TacticM Unit) : TacticM Unit := do
  let lbrak := rwRulesSeqStx[0]
  let rules := rwRulesSeqStx[1].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext lbrak (pure ())
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]!
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    -- show rule state up to (incl.) next `,`
    withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        -- let processId (id : Syntax) : TacticM Unit := do
        x symm term

/--
`simp_rw` functions as a mix of `simp` and `rw`. Like `rw`, it applies each
rewrite rule in the given order, but like `simp` it repeatedly applies these
rules and also under binders like `∀ x, ...`, `∃ x, ...` and `fun x ↦...`.
Usage:

- `simp_rw [lemma_1, ..., lemma_n]` will rewrite the goal by applying the
  lemmas in that order. A lemma preceded by `←` is applied in the reverse direction.
- `simp_rw [lemma_1, ..., lemma_n] at h₁ ... hₙ` will rewrite the given hypotheses.
- `simp_rw [...] at *` rewrites in the whole context: all hypotheses and the goal.

Lemmas passed to `simp_rw` must be expressions that are valid arguments to `simp`.
For example, `rw` cannot directly solve the following, but `simp_rw` can:

```lean
example {a : ℕ}
    (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
    (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
    (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 := by
  simp_rw [h1, h2]
```

`simp` also solves the goal above, but it does not show the step-by-step transformation of the goal
that `simp_rw` shows. `rw` cannot solve this directly because it cannot rewrite expressions
containing bound variables (https://github.com/leanprover/lean4/issues/6033). With `conv` and
`intro`, `rw` can be used:

```lean
example {a : ℕ}
    (h1 : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
    (h2 : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
    (∀ b, a - 1 ≤ b) = ∀ b c : ℕ, c < a → c < b + 1 := by
  conv_lhs =>
    intro
    rw [h1, h2]
```

Internally, `simp_rw [lemma_1, ..., lemma_n]` is equivalent to
```
simp only [lemma_1]
...
simp only [lemma_n]
```

This tactic also accepts `simp`'s config options, see
https://lean-lang.org/doc/reference/latest/The-Simplifier/Configuring-Simplification.
For example:

```lean
example (a b c d : ℕ) (h : a = c + d) : b + a = b + c + d := by
  simp_rw +arith [h]
```

The option `+arith` allows `simp` to simplify `b + (c + d)` to `b + c + d` after replacing `a`
with `c + d`.

Unlike `rw`, `simp_rw` cannot introduce new subgoals for conditional rewrite rules.
For example, the following works with `rw`, but not `simp_rw`:

```lean
example (a b c : ℕ) (h1 : a = b → b = c → a = c) (h2 : a = b) (h3 : b = c) : a + 1 = c + 1 := by
  rw [h1]
  -- The rewrite rule `a = c` is applied on the goal, closing it.
  -- The two hypotheses `a = b` and `b = c` of `h1` are created as subgoals.
  · exact h2
  · exact h3
```
-/
elab s:"simp_rw " cfg:optConfig rws:rwRuleSeq g:(location)? : tactic => focus do
  evalTactic (← `(tactic| simp%$s $[$(getConfigItems cfg)]* (failIfUnchanged := false) only $(g)?))
  withSimpRWRulesSeq rws fun symm term => do
    evalTactic (← match term with
    | `(term| $e:term) =>
      if symm then
        `(tactic| simp%$e $cfg only [← $e:term] $g ?)
      else
        `(tactic| simp%$e $cfg only [$e:term] $g ?))

end Mathlib.Tactic
