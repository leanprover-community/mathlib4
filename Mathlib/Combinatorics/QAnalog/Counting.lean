/-
Copyright (c) 2026 Alessandro Iraci, Giovanni Paolini, Aristotle contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro Iraci, Giovanni Paolini, Aristotle (Harmonic)
-/
module

public import Mathlib.Combinatorics.QAnalog.Binomial
public import Mathlib.Data.Finset.Powerset

/-!
# `q`-binomial coefficients as generating functions for subsets

The `q`-binomial coefficient `[n choose k]_q` is the generating function, by the number of
inversions, of the `k`-element subsets of `{0, …, n - 1}`:

`∑_{T ⊆ range n, #T = k} q ^ (inversions T) = [n choose k]_q`,

where an inversion of `T` is a pair `s < t` with `t ∈ T` and `s ∉ T`.  Since a `k`-element set
`T = {t₀ < ⋯ < t_{k-1}}` has `∑ T - (k choose 2)` inversions, this is equivalent to

`∑_{T ⊆ range n, #T = k} q ^ (∑ T) = q ^ (k choose 2) * [n choose k]_q`.

## Main definitions

* `QAnalog.inversions T`, the number of inversions of a finite set of natural numbers.

## Main results

* `QAnalog.sum_pow_inversions_eq_qBinomial`: the first identity above.
* `QAnalog.sum_pow_sum_eq_qBinomial`: the second identity above.
-/

open Finset

variable {R : Type*} [Semiring R]

namespace QAnalog

/-- The number of inversions of a finite set `T` of natural numbers: the number of pairs `s < t`
with `t ∈ T` and `s ∉ T`.  For a `k`-element subset of `range n` this is a natural number at most
`k * (n - k)`, and it equals `∑ T - (k choose 2)`. -/
def inversions (T : Finset ℕ) : ℕ := ∑ t ∈ T, #{s ∈ range t | s ∉ T}

@[simp] theorem inversions_empty : inversions ∅ = 0 := by simp [inversions]

/-! ### Splitting subsets of `range (n + 1)` according to whether they contain `0` -/

/-- The shift `n ↦ n + 1`, as an embedding. -/
private def succEmb : ℕ ↪ ℕ := ⟨fun n => n + 1, fun _ _ h => by simpa using h⟩

@[simp] private lemma succEmb_apply (n : ℕ) : succEmb n = n + 1 := rfl

private lemma range_succ_eq_insert_map (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map succEmb) := by
  ext x
  simp only [mem_range, mem_insert, mem_map, succEmb_apply]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr ⟨x - 1, by omega, by omega⟩
  · rintro (rfl | ⟨a, ha, rfl⟩) <;> omega

/-- Every `(k+1)`-element subset of `range (n + 1)` is either the shift of a `(k+1)`-element
subset of `range n`, or `0` together with the shift of a `k`-element subset of `range n`. -/
private lemma sum_powersetCard_succ (f : Finset ℕ → R) (n k : ℕ) :
    ∑ T ∈ (range (n + 1)).powersetCard (k + 1), f T
      = (∑ T ∈ (range n).powersetCard (k + 1), f (T.map succEmb))
        + ∑ T ∈ (range n).powersetCard k, f (insert 0 (T.map succEmb)) := by
  rw [range_succ_eq_insert_map, Finset.powersetCard_succ_insert (by simp), Finset.sum_union]
  · congr 1
    · rw [Finset.powersetCard_map, Finset.sum_map]
      rfl
    · rw [Finset.powersetCard_map, Finset.sum_image, Finset.sum_map]
      · rfl
      · intro A hA B hB hAB
        simp only [Finset.mem_coe, Finset.mem_map, RelEmbedding.coe_toEmbedding,
          Finset.mapEmbedding_apply] at hA hB
        obtain ⟨TA, -, rfl⟩ := hA
        obtain ⟨TB, -, rfl⟩ := hB
        have hA0 : (0 : ℕ) ∉ TA.map succEmb := by simp
        have hB0 : (0 : ℕ) ∉ TB.map succEmb := by simp
        have := congrArg (fun s => Finset.erase s 0) hAB
        simpa [Finset.erase_insert, hA0, hB0] using this
  · refine Finset.disjoint_left.2 fun A hA hA' => ?_
    have h1 : (0 : ℕ) ∉ A := by
      rw [Finset.mem_powersetCard] at hA
      intro h0
      have := hA.1 h0
      simp at this
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hA'
    exact h1 (Finset.mem_insert_self 0 B)

/-! ### The generating function by inversions -/

private lemma filter_notMem_map (T : Finset ℕ) (t : ℕ) :
    {s ∈ range (t + 1) | s ∉ T.map succEmb} = insert 0 (({s ∈ range t | s ∉ T}).map succEmb) := by
  ext s
  cases s with
  | zero => simp
  | succ u => simp

private lemma filter_notMem_insert_zero_map (T : Finset ℕ) (t : ℕ) :
    {s ∈ range (t + 1) | s ∉ insert 0 (T.map succEmb)}
      = ({s ∈ range t | s ∉ T}).map succEmb := by
  ext s
  cases s with
  | zero => simp
  | succ u => simp

@[simp] theorem inversions_map_succ (T : Finset ℕ) :
    inversions (T.map succEmb) = inversions T + #T := by
  rw [inversions, Finset.sum_map]
  have h : ∀ t : ℕ, #{s ∈ range (t + 1) | s ∉ T.map succEmb} = #{s ∈ range t | s ∉ T} + 1 :=
    fun t => by rw [filter_notMem_map, Finset.card_insert_of_notMem (by simp), card_map]
  simp only [succEmb_apply, h]
  rw [Finset.sum_add_distrib, inversions]
  simp

@[simp] theorem inversions_insert_zero_map (T : Finset ℕ) :
    inversions (insert 0 (T.map succEmb)) = inversions T := by
  rw [inversions, Finset.sum_insert (by simp), Finset.sum_map]
  simp only [succEmb_apply, filter_notMem_insert_zero_map, card_map, range_zero]
  simp [inversions]

/-- **The `q`-binomial coefficient counts subsets by inversions**: the generating function, by
number of inversions, of the `k`-element subsets of `{0, …, n - 1}` is `[n choose k]_q`. -/
theorem sum_pow_inversions_eq_qBinomial (q : R) (n k : ℕ) :
    ∑ T ∈ (range n).powersetCard k, q ^ inversions T = qBinomial q n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => rw [Finset.range_zero, Finset.powersetCard_eq_empty.2 (by simp)]; simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [sum_powersetCard_succ, qBinomial_succ_succ, add_comm]
      congr 1
      · rw [← ih k]
        exact Finset.sum_congr rfl fun T _ => by rw [inversions_insert_zero_map]
      · rw [← ih (k + 1), Finset.mul_sum]
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [inversions_map_succ, (Finset.mem_powersetCard.1 hT).2, pow_add, pow_mul_comm]

/-- Since a `k`-element subset `T` of `range n` has `∑ T - (k choose 2)` inversions, the
generating function of the `k`-element subsets of `{0, …, n - 1}` by the sum of their elements is
`q ^ (k choose 2) * [n choose k]_q`. -/
theorem sum_pow_sum_eq_qBinomial (q : R) (n k : ℕ) :
    ∑ T ∈ (range n).powersetCard k, q ^ (∑ t ∈ T, t) = q ^ (k.choose 2) * qBinomial q n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => rw [Finset.range_zero, Finset.powersetCard_eq_empty.2 (by simp)]; simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hchoose : (k + 1).choose 2 = k.choose 2 + k := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
      have hmap : ∀ T : Finset ℕ, ∑ t ∈ T.map succEmb, t = (∑ t ∈ T, t) + #T := fun T => by
        rw [Finset.sum_map]; simp [Finset.sum_add_distrib]
      rw [sum_powersetCard_succ, qBinomial_succ_succ, hchoose]
      -- the sums over the two halves, each factored as a power of `q` times a smaller sum
      have e1 : ∑ T ∈ (range n).powersetCard (k + 1), q ^ (∑ t ∈ T.map succEmb, t)
          = (∑ T ∈ (range n).powersetCard (k + 1), q ^ (∑ t ∈ T, t)) * q ^ (k + 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun T hT => by
          rw [hmap, (Finset.mem_powersetCard.1 hT).2, pow_add]
      have e2 : ∑ T ∈ (range n).powersetCard k, q ^ (∑ t ∈ insert 0 (T.map succEmb), t)
          = (∑ T ∈ (range n).powersetCard k, q ^ (∑ t ∈ T, t)) * q ^ k := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun T hT => by
          rw [Finset.sum_insert (by simp), hmap, (Finset.mem_powersetCard.1 hT).2, zero_add,
            pow_add]
      have h1 : ∑ T ∈ (range n).powersetCard (k + 1), q ^ (∑ t ∈ T.map succEmb, t)
          = q ^ (k.choose 2 + k) * (q ^ (k + 1) * qBinomial q n (k + 1)) := by
        rw [e1, ← hchoose, ih (k + 1), mul_assoc,
          ← (qBinomial_commute_pow q (k + 1) n (k + 1)).eq]
      have h2 : ∑ T ∈ (range n).powersetCard k, q ^ (∑ t ∈ insert 0 (T.map succEmb), t)
          = q ^ (k.choose 2 + k) * qBinomial q n k := by
        rw [e2, ih k, mul_assoc, ← (qBinomial_commute_pow q k n k).eq, ← mul_assoc, ← pow_add]
      rw [h1, h2, mul_add, add_comm]

end QAnalog
