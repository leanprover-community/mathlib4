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

## Main definitions

* `InformationTheory.kraftWeight`: the weight `(1 / D) ^ |w|` of a word over an alphabet of size
  `D`.

## Main results

* `InformationTheory.kraft_inequality`: the Kraft sum of a finite prefix-free code is at most one.
* `InformationTheory.summable_kraftWeight`: the Kraft weights of an arbitrary prefix-free code
  are summable.
* `InformationTheory.kraft_inequality_infinite`: the Kraft sum of an arbitrary prefix-free code
  is at most one.

## References

* Cover and Thomas, *Elements of Information Theory*, Chapter 5.
-/

@[expose] public section

namespace InformationTheory

variable {α : Type*} [Fintype α] [Nonempty α]

/-- The Kraft weight of a word over the alphabet `α` is `(1 / |α|) ^ |w|`. -/
noncomputable def kraftWeight (w : List α) : ℝ :=
  (1 / (Fintype.card α : ℝ)) ^ w.length

/-- **Kraft's inequality.** The sum of the Kraft weights of a finite prefix-free code is at most
one. -/
theorem kraft_inequality {S : Finset (List α)} (hS : PrefixFree (S : Set (List α))) :
    ∑ w ∈ S, kraftWeight w ≤ 1 := by
  by_cases hε : [] ∈ S
  · have hS' : S = {[]} := by
      exact_mod_cast hS.epsilon_singleton hε
    simp [hS', kraftWeight]
  · simpa [kraftWeight] using kraft_mcmillan_inequality (hS.uniquely_decodable hε)

private lemma sum_kraftWeight_le_one {S : Set (List α)} (hS : PrefixFree S) (F : Finset S) :
    ∑ w ∈ F, kraftWeight (w : List α) ≤ 1 := by
  classical
  let T : Finset (List α) := F.image Subtype.val
  have hTS : (T : Set (List α)) ⊆ S := by
    intro w hw
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hw
    exact w.2
  calc
    ∑ w ∈ F, kraftWeight (w : List α) = ∑ w ∈ T, kraftWeight w := by simp [T]
    _ ≤ 1 := kraft_inequality (hS.mono hTS)

/-- The Kraft weights of an arbitrary prefix-free code are summable. -/
theorem summable_kraftWeight {S : Set (List α)} (hS : PrefixFree S) :
    Summable (fun w : S ↦ kraftWeight (w : List α)) :=
  summable_of_sum_le (fun _ ↦ by unfold kraftWeight; positivity) (sum_kraftWeight_le_one hS)

/-- **Kraft's inequality for arbitrary codes.** The sum of the Kraft weights of an arbitrary
prefix-free code is at most one. -/
theorem kraft_inequality_infinite {S : Set (List α)} (hS : PrefixFree S) :
    ∑' w : S, kraftWeight (w : List α) ≤ 1 :=
  (summable_kraftWeight hS).tsum_le_of_sum_le (sum_kraftWeight_le_one hS)

end InformationTheory
