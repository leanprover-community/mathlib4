/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Tactic.Basic
import Aesop

/-!
# SetLike Rule Set

This module defines the `SetLike` and `SetLike!` Aesop rule sets.
Aesop rule sets only become visible once the file in which they're declared is imported,
so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [SetLike] (default := true)
declare_aesop_rule_sets [SetLike!] (default := false)

library_note2 «SetLike Aesop ruleset» /--
The Aesop tactic (`aesop`) can automatically prove obvious facts about membership in structures
such as subgroups and subrings. Certain lemmas regarding membership in algebraic substructures
are given the `aesop` attribute according to the following principles:
- Rules are in the `SetLike` ruleset: (rule_sets := [SetLike]).
- Apply-style rules with trivial hypotheses are registered both as `simp` rules and as
  `safe` Aesop rules. The latter is needed in case there are metavariables in the goal.
  For instance, Aesop can use the rule `one_mem` to prove
  `(M : Type*) [Monoid M] (s : Submonoid M) ⊢ ∃ m : M, m ∈ s`.
- Apply-style rules with nontrivial hypotheses are marked `unsafe`. This is because applying them
  might not be provability-preserving in the context of more complex membership rules.
  For instance, `mul_mem` is marked `unsafe`.
  - Unsafe rules are given a probability no higher than 90%. This is the same probability
    Aesop gives to safe rules when they generate metavariables. If the priority is too high, loops
    generated in the presence of metavariables will time out Aesop.
  - Rules that cause loops (even in the absence of metavariables) are given a low priority of 5%.
    These rules are placed in the `SetLike!` ruleset instead of the `SetLike` ruleset so that
    they are not invoked by default. An example is `SetLike.mem_of_subset`.
  - Simplifying the left-hand side of a membership goal is prioritised over simplifying the
    right-hand side. By default, rules simplifying the LHS (e.g., `mul_mem`) are given
    probability 90% and rules simplifying the RHS are given probability 80%
    (e.g., `Subgroup.mem_closure_of_mem`).
  - These default probabilities are for rules with simple hypotheses that fail quickly when
    not satisfied, such as `mul_mem`. Rules with more complicated hypotheses, or rules that are
    less likely to progress the proof state towards a solution, are given a lower priority.
- To optimise performance and avoid timeouts, Aesop should not be invoking low-priority rules
  unless it can make no other progress. If common usage patterns cause Aesop to invoke such rules,
  additional lemmas are added at a higher priority to cover that pattern.
  For example, `Subgroup.mem_closure_of_mem` covers a common use case of `SetLike.mem_of_subset`.

Some examples of membership-related goals which Aesop with this ruleset is designed to close
can be found in the file MathlibTest/set_like.lean.
-/
