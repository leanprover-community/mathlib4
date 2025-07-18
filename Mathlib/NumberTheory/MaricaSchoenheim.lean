/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SetFamily.FourFunctions
import Mathlib.Data.Nat.Squarefree

/-!
# The Marica-Schönheim special case of Graham's conjecture

Graham's conjecture states that if $0 < a_1 < \dots a_n$ are integers, then
$\max_{i, j} \frac{a_i}{\gcd(a_i, a_j)} \ge n$. This file proves the conjecture when the $a_i$ are
squarefree as a corollary of the Marica-Schönheim inequality.

## References

[*Applications of the FKG Inequality and Its Relatives*, Graham][Graham1983]
-/

open Finset
open scoped FinsetFamily

namespace Nat

/-- Statement of Graham's conjecture (which is now a theorem in the literature).

Graham's conjecture states that if $0 < a_1 < \dots a_n$ are integers, then
$\max_{i, j} \frac{a_i}{\gcd(a_i, a_j)} \ge n$. -/
def GrahamConjecture (n : ℕ) (f : ℕ → ℕ) : Prop :=
  n ≠ 0 → StrictMonoOn f (Set.Iio n) → ∃ i < n, ∃ j < n, (f i).gcd (f j) * n ≤ f i

/-- The special case of Graham's conjecture where all numbers are squarefree. -/
lemma grahamConjecture_of_squarefree {n : ℕ} (f : ℕ → ℕ) (hf' : ∀ k < n, Squarefree (f k)) :
    GrahamConjecture n f := by
  rintro hn hf
  by_contra!
  set 𝒜 := (Iio n).image fun n ↦ primeFactors (f n)
  have hf'' : ∀ i < n, ∀ j, Squarefree (f i / (f i).gcd (f j)) :=
    fun i hi j ↦ (hf' _ hi).squarefree_of_dvd <| div_dvd_of_dvd <| gcd_dvd_left _ _
  refine lt_irrefl n ?_
  calc
    n = #𝒜 := ?_
    _ ≤ #(𝒜 \\ 𝒜) := 𝒜.card_le_card_diffs
    _ ≤ #(Ioo 0 n) := card_le_card_of_injOn (fun s ↦ ∏ p ∈ s, p) ?_ ?_
    _ = n - 1 := by rw [card_Ioo, tsub_zero]
    _ < n := tsub_lt_self hn.bot_lt zero_lt_one
  · rw [Finset.card_image_of_injOn, card_Iio]
    simpa using prod_primeFactors_invOn_squarefree.2.injOn.comp hf.injOn hf'
  · simp only [𝒜, forall_mem_diffs, forall_mem_image, mem_Ioo, mem_Iio, Set.MapsTo, mem_coe]
    rintro i hi j hj
    rw [← primeFactors_div_gcd (hf' _ hi) (hf' _ hj).ne_zero,
      prod_primeFactors_of_squarefree <| hf'' _ hi _]
    exact ⟨Nat.div_pos (gcd_le_left _ (hf' _ hi).ne_zero.bot_lt) <|
      Nat.gcd_pos_of_pos_left _ (hf' _ hi).ne_zero.bot_lt, Nat.div_lt_of_lt_mul <| this _ hi _ hj⟩
  · simp only [𝒜, Set.InjOn, mem_coe, forall_mem_diffs, forall_mem_image, mem_Iio]
    rintro a ha b hb c hc d hd
    rw [← primeFactors_div_gcd (hf' _ ha) (hf' _ hb).ne_zero, ← primeFactors_div_gcd
      (hf' _ hc) (hf' _ hd).ne_zero, prod_primeFactors_of_squarefree (hf'' _ ha _),
      prod_primeFactors_of_squarefree (hf'' _ hc _)]
    rintro h
    rw [h]

end Nat
