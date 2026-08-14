/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.InformationTheory.Coding.PrefixFree
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Kraft's Inequality

This file proves Kraft's inequality for prefix-free codes over finite alphabets. The finite result
is an immediate consequence of the Kraft–McMillan inequality; the result for arbitrary sets of
codewords follows by bounding every finite partial sum.

## Main results

* `IsPrefixFree.finsetSum_one_div_card_pow_length_le_one`: the Kraft sum of a finite prefix-free
  code is at most one.
* `summable_one_div_card_pow_length`: the Kraft sum of an arbitrary prefix-free code is summable.
* `tsum_one_div_card_pow_length_le_one`: the Kraft sum of an arbitrary prefix-free code is at most
  one.

## References

* Cover and Thomas, *Elements of Information Theory*, Chapter 5.
-/

public section

namespace InformationTheory

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **Kraft's inequality.** The Kraft sum of a finite prefix-free code is at most one. -/
theorem IsPrefixFree.finsetSum_one_div_card_pow_length_le_one
    {S : Finset (List α)} (hS : IsPrefixFree (S : Set (List α))) :
    ∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length ≤ 1 := by
  by_cases hε : [] ∈ S
  · have hS' : S = {[]} := by
      exact_mod_cast hS.eq_singleton_empty_of_empty_mem hε
    simp [hS']
  · exact (hS.isUniquelyDecodable hε).finsetSum_one_div_card_pow_length_le_one

private lemma finsetSum_one_div_card_pow_length_of_subtype
    {S : Set (List α)} (hS : IsPrefixFree S) (F : Finset S) :
    ∑ w ∈ F, (1 / (Fintype.card α : ℝ)) ^ (w : List α).length ≤ 1 := by
  classical
  let T : Finset (List α) := F.image Subtype.val
  have hTS : (T : Set (List α)) ⊆ S := by grind
  calc
    ∑ w ∈ F, (1 / (Fintype.card α : ℝ)) ^ (w : List α).length =
        ∑ w ∈ T, (1 / (Fintype.card α : ℝ)) ^ w.length := by simp [T]
    _ ≤ 1 := (hS.anti hTS).finsetSum_one_div_card_pow_length_le_one

/-- The Kraft sum of an arbitrary prefix-free code is summable. -/
theorem summable_one_div_card_pow_length {S : Set (List α)} (hS : IsPrefixFree S) :
    Summable (fun w : S ↦ (1 / (Fintype.card α : ℝ)) ^ (w : List α).length) :=
  summable_of_sum_le (fun _ ↦ by positivity) (finsetSum_one_div_card_pow_length_of_subtype hS)

/-- **Kraft's inequality for arbitrary codes.** The Kraft sum of an arbitrary prefix-free code is
at most one. -/
theorem tsum_one_div_card_pow_length_le_one {S : Set (List α)} (hS : IsPrefixFree S) :
    ∑' w : S, (1 / (Fintype.card α : ℝ)) ^ (w : List α).length ≤ 1 :=
  (summable_one_div_card_pow_length hS).tsum_le_of_sum_le
    (finsetSum_one_div_card_pow_length_of_subtype hS)

end InformationTheory
