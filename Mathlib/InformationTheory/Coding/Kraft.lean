/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.InformationTheory.Coding.PrefixFree
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.InformationTheory.Coding.KraftMcMillan

/-!
# Kraft's Inequality

This file proves Kraft's inequality for prefix-free codes over finite alphabets. The finite result
is an immediate consequence of the Kraft–McMillan inequality; the result for arbitrary sets of
codewords follows by bounding every finite partial sum.

## Main results

* `InformationTheory.kraft_inequality`: the Kraft sum of a finite prefix-free code is at most one.
* `InformationTheory.summable_kraft_sum`: the Kraft sum of an arbitrary prefix-free code is
  summable.
* `InformationTheory.kraft_inequality_infinite`: the Kraft sum of an arbitrary prefix-free code
  is at most one.

## References

* Cover and Thomas, *Elements of Information Theory*, Chapter 5.
-/

@[expose] public section

namespace InformationTheory

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **Kraft's inequality.** The Kraft sum of a finite prefix-free code is at most one. -/
theorem kraft_inequality {S : Finset (List α)} (hS : PrefixFree (S : Set (List α))) :
    ∑ w ∈ S, (1 / (Fintype.card α : ℝ)) ^ w.length ≤ 1 := by
  by_cases hε : [] ∈ S
  · have hS' : S = {[]} := by
      exact_mod_cast hS.eq_singleton_empty_of_empty_mem hε
    simp [hS']
  · exact kraft_mcmillan_inequality (hS.uniquelyDecodable hε)

private lemma sum_kraft_le_one {S : Set (List α)} (hS : PrefixFree S) (F : Finset S) :
    ∑ w ∈ F, (1 / (Fintype.card α : ℝ)) ^ (w : List α).length ≤ 1 := by
  classical
  let T : Finset (List α) := F.image Subtype.val
  have hTS : (T : Set (List α)) ⊆ S := by grind
  calc
    ∑ w ∈ F, (1 / (Fintype.card α : ℝ)) ^ (w : List α).length =
        ∑ w ∈ T, (1 / (Fintype.card α : ℝ)) ^ w.length := by simp [T]
    _ ≤ 1 := kraft_inequality (hS.mono hTS)

/-- The Kraft sum of an arbitrary prefix-free code is summable. -/
theorem summable_kraft_sum {S : Set (List α)} (hS : PrefixFree S) :
    Summable (fun w : S ↦ (1 / (Fintype.card α : ℝ)) ^ (w : List α).length) :=
  summable_of_sum_le (fun _ ↦ by positivity) (sum_kraft_le_one hS)

/-- **Kraft's inequality for arbitrary codes.** The Kraft sum of an arbitrary prefix-free code is
at most one. -/
theorem kraft_inequality_infinite {S : Set (List α)} (hS : PrefixFree S) :
    ∑' w : S, (1 / (Fintype.card α : ℝ)) ^ (w : List α).length ≤ 1 :=
  (summable_kraft_sum hS).tsum_le_of_sum_le (sum_kraft_le_one hS)

end InformationTheory
