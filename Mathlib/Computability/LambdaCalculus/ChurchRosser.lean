/-
Copyright (c) 2026 zayn7lie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Wang
-/
import Mathlib.Computability.LambdaCalculus.ConfluentReduction
import Mathlib.Computability.LambdaCalculus.ParallelReduction

/-!
# The Church–Rosser theorem for β-reduction

This file proves confluence of β-reduction on de Bruijn lambda terms.  The proof follows
the classical route:

1. define parallel β-reduction,
2. show that parallel reduction has the diamond property using complete developments,
3. compare parallel reduction with ordinary β-reduction via reflexive-transitive closure,
4. transport confluence back to β-reduction.

## Main results

* `diamond_par`: parallel reduction is diamond.
* `churchRosser_beta`: β-reduction is confluent.

## Implementation note

The proof relies on the generic rewriting lemmas from `ConfluentReduction` together with
the complete-development machinery from `ParallelReduction`.
-/

namespace Lambda
open Term

/-- Parallel Reduction is Diamond. -/
lemma diamond_par : Diamond Par := by
  intro a b c hab hac
  exact ⟨a.dev, par_to_dev hab, par_to_dev hac⟩

/-- Church–Rosser: β is confluent (on RTC). -/
theorem churchRosser_beta : Confluent Beta := by
  -- Confluence of Par from diamond
  have hPar : Confluent Par :=
    confluent_of_diamond (r := Par) diamond_par
  -- Identify BetaStar and ParStar via sandwich
  have hEq {a b : Term} : BetaStar a b ↔ ParStar a b :=
      rtc_eq_of_sandwich (r := Beta) (p := Par)
    (by intro a b h; exact beta_subset_par h)
    (by intro a b h; exact par_subset_betaStar h)
  -- Transport confluence
  intro a b c hab hac
  have hab' : ParStar a b := (hEq).1 hab
  have hac' : ParStar a c := (hEq).1 hac
  rcases hPar hab' hac' with ⟨d, hbd, hcd⟩
  exact ⟨d, (hEq).2 hbd, (hEq).2 hcd⟩

end Lambda
