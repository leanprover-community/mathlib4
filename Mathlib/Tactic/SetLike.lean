/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Init
import Aesop

/-!
# SetLike Rule Set

This module defines the `SetLike` and `SetLike!` Aesop rule sets.
Aesop rule sets only become visible once the file in which they're declared is imported,
so we must put this declaration into its own file.
-/

declare_aesop_rule_sets [SetLike] (default := true)
declare_aesop_rule_sets [SetLike!] (default := false)

library_note "SetLike Aesop ruleset"/--
The Aesop tactic (`aesop`) can automatically prove obvious facts about membership in structures
such as subgroups and subrings. Certain lemmas regarding membership in algebraic substructures
are given the `aesop` attribute according to the following principles:
- Rules are in the `SetLike` ruleset: (rule_sets := [SetLike]).
- Apply-style rules with trivial hypotheses are registered both as `simp` rules and as
  `safe` Aesop rules. The latter is needed in case there are metavariables in the goal.
  For instance, Aesop can use the rule `one_mem` to prove
  `(M : Type*) [Monid M] (s : Submonoid M) ⊢ ∃ m : M, m ∈ s`.
- Apply-style rules with nontrivial hypotheses are marked `unsafe`. This is because applying them
  might not be provability-preserving in the context of more complex membership rules.
  For instance, `mul_mem` is marked `unsafe`.
- Unsafe rules should not be given a priority higher than 90%. This is the same probability
  Aesop gives to safe rules when they generate metavariables. If the priority is too high, loops
  generated in the presence of metavariables will time out Aesop.
- Apply-style rules with simple hypotheses which are refuted quickly if they aren't provable
  are given probability 90%. An example is `mul_mem`.
- Rules that cause loops (even in the absence of metavariables) are given a priority of 5%.
  For performance reasons, these rules are placed in the `SetLike!` ruleset instead of the
  `SetLike` ruleset. An example is `SetLike.mem_of_subset`.
- All other `unsafe` rules are given a probability between 5% and 90% based on how likely they are
  to progress the proof state towards a solution. Apply-style rules should be given a higher
  probability the more specific their conclusions are and the more generic their hypotheses are.
  For instance, `Subgroup.mem_closure_of_mem` is given a lower probability than `mul_mem` because
  its conclusion is more generic.
- To optimise performance and avoid timeouts, Aesop should not be invoking low-priority rules
  unless it can make no other progress. If common usage patterns cause Aesop to invoke such rules,
  additional lemmas should be added at a higher priority to cover that pattern.
  For example, `Subgroup.closure_mem_of_mem` covers a common use case of `SetLike.mem_of_subset`.

Some examples of membership-related goals which Aesop this ruleset is designed to close
can be found in the file MathlibTest/set_like.lean.
-/
