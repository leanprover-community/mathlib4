/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández, Yu Shao, Beibei Xiong, Weijie Jiang,
Yi Yuan
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-! # Bell numbers for multisets

For `n : ℕ`, the `n`th Bell number is the number of partitions of a set of cardinality `n`.
Here, we define a refinement of these numbers, that count, for any `m : Multiset ℕ`,
the number of partitions of a set of cardinality `m.sum` whose parts have cardinalities
given by `m`.

The definition presents it as a natural number.

* `Multiset.bell`: number of partitions of a set whose parts have cardinalities a given multiset

* `Nat.uniformBell m n` : short name for `Multiset.bell (replicate m n)`

* `Multiset.bell_mul_eq` shows that
  `m.bell * (m.map (fun j ↦ j !)).prod * Π j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum !`

* `Nat.uniformBell_mul_eq`  shows that
  `uniformBell m n * n ! ^ m * m ! = (m * n) !`

* `Nat.uniformBell_succ_left` computes `Nat.uniformBell (m + 1) n` from `Nat.uniformBell m n`

* `Nat.bell n`: the `n`th standard Bell number,
  which counts the number of partitions of a set of cardinality `n`

* `Nat.bell_succ n` shows that
  `Nat.bell (n + 1) = ∑ k ∈ Finset.range (n + 1), Nat.choose n k * Nat.bell (n - k)`

## TODO

Prove that it actually counts the number of partitions as indicated.
(When `m` contains `0`, the result requires to admit repetitions of the empty set as a part.)

-/

@[expose] public section

open Multiset Nat

namespace Multiset

/-- Number of partitions of a set of cardinality `m.sum`
whose parts have cardinalities given by `m` -/
def bell (m : Multiset ℕ) : ℕ :=
  Nat.multinomial m.toFinset (fun k ↦ k * m.count k) *
    ∏ k ∈ m.toFinset.erase 0, ∏ j ∈ .range (m.count k), (j * k + k - 1).choose (k - 1)

@[simp]
theorem bell_zero : bell 0 = 1 := rfl

private theorem bell_mul_eq_lemma {x : ℕ} (hx : x ≠ 0) :
    ∀ c, x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1) = (x * c)!
  | 0 => by simp
  | c + 1 => calc
      x ! ^ (c + 1) * (c + 1)! * ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1)
        = x ! * (c + 1) * x ! ^ c * c ! *
            ∏ j ∈ Finset.range (c + 1), (j * x + x - 1).choose (x - 1) := by
        rw [factorial_succ, pow_succ]; ring
      _ = (x ! ^ c * c ! * ∏ j ∈ Finset.range c, (j * x + x - 1).choose (x - 1)) *
            (c * x + x - 1).choose (x - 1) * x ! * (c + 1) := by
        rw [Finset.prod_range_succ]; ring
      _ = (c + 1) * (c * x + x - 1).choose (x - 1) * (x * c)! * x ! := by
        rw [bell_mul_eq_lemma hx]; ring
      _ = (x * (c + 1))! := by
        rw [← Nat.choose_mul_add hx, mul_comm c x, Nat.add_choose_mul_factorial_mul_factorial]
        ring_nf

theorem bell_mul_eq (m : Multiset ℕ) :
    m.bell * (m.map (fun j ↦ j !)).prod * ∏ j ∈ (m.toFinset.erase 0), (m.count j)! = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i ∈ m.toFinset, (i * count i m)!) (by positivity)]
  simp only [← mul_assoc, Nat.multinomial_spec]
  rw [mul_assoc, mul_assoc, mul_comm]
  congr
  · rw [mul_comm, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_multiset_map_count]
    suffices this : _ by
      by_cases hm : 0 ∈ m.toFinset
      · rw [← Finset.prod_erase_mul _ _ hm]
        rw [← Finset.prod_erase_mul _ _ hm]
        simp only [factorial_zero, one_pow, mul_one, zero_mul]
        exact this
      · nth_rewrite 1 [← Finset.erase_eq_of_notMem hm]
        nth_rewrite 3 [← Finset.erase_eq_of_notMem hm]
        exact this
    rw [← Finset.prod_mul_distrib]
    congr! 1 with x hx
    rw [← mul_assoc, bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]

theorem bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map fun j ↦ j !).prod * ∏ j ∈ m.toFinset.erase 0, (m.count j)!) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    exact Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)

private theorem bell_cons_mul_count (m : Multiset ℕ) {a : ℕ} (ha : a ≠ 0) :
    (a ::ₘ m).bell * (a ::ₘ m).count a = (m.sum + a).choose a * m.bell := by
  let rest := ∏ j ∈ (m.toFinset.erase 0).erase a, (m.count j)!
  have hrest : rest = ∏ j ∈ ((a ::ₘ m).toFinset.erase 0).erase a, ((a ::ₘ m).count j)! := by
    unfold rest
    congr! 1 with j hj
    · grind [Multiset.toFinset_cons]
    · simp [Finset.mem_erase.mp hj]
  let c := (m.map (· !)).prod * (m.count a)! * rest
  have hm0 : m.bell * c = m.sum ! := by
    have hsplit : (m.count a)! * rest = ∏ j ∈ m.toFinset.erase 0, (m.count j)! := by
      by_cases hmem : a ∈ m.toFinset.erase 0
      · rw [← Finset.mul_prod_erase _ _ hmem]
      · have hcount : m.count a = 0 := by grind [Multiset.count_eq_zero_of_notMem]
        simp [rest, Finset.erase_eq_of_notMem hmem, hcount]
    simpa [c, hsplit, mul_assoc] using Multiset.bell_mul_eq m
  have hm : m.sum ! * a ! = m.bell * a ! * c := by grind
  have hc : 0 < a ! * c := Nat.mul_pos (by positivity) <|
    Nat.mul_pos (by simp [Nat.factorial_pos]) (by positivity)
  apply Nat.eq_of_mul_eq_mul_right hc
  calc
    _ = (m.sum + a)! := by
      have hq := Multiset.bell_mul_eq (a ::ₘ m)
      rw [← Finset.mul_prod_erase _ _ (a := a) (by simp [*]), ← hrest] at hq
      simpa [c, Nat.factorial_succ, add_comm, mul_assoc, mul_left_comm] using hq
    _ = ((m.sum + a).choose a * m.bell) * (a ! * c) := by
      simp [← Nat.add_choose_mul_factorial_mul_factorial, mul_assoc, hm]

end Multiset

namespace Nat

/-- Number of possibilities of dividing a set with `m * n` elements into `m` groups
of `n`-element subsets. -/
def uniformBell (m n : ℕ) : ℕ := bell (replicate m n)

theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), choose (p * n + n - 1) (n - 1) := by
  unfold uniformBell bell
  rw [toFinset_replicate]
  split_ifs with hm
  · simp [hm]
  · by_cases hn : n = 0
    · simp [hn]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp [count_replicate]

theorem uniformBell_zero_left (n : ℕ) : uniformBell 0 n = 1 := by
  simp [uniformBell_eq]

theorem uniformBell_zero_right (m : ℕ) : uniformBell m 0 = 1 := by
  simp [uniformBell_eq]

theorem uniformBell_succ_left (m n : ℕ) :
    uniformBell (m + 1) n = choose (m * n + n - 1) (n - 1) * uniformBell m n := by
  simp only [uniformBell_eq, Finset.prod_range_succ, mul_comm]

theorem uniformBell_one_left (n : ℕ) : uniformBell 1 n = 1 := by
  simp only [uniformBell_eq, Finset.range_one, Finset.prod_singleton, zero_mul,
    zero_add, choose_self]

theorem uniformBell_one_right (m : ℕ) : uniformBell m 1 = 1 := by
  simp only [uniformBell_eq, mul_one, add_tsub_cancel_right, le_refl,
    tsub_eq_zero_of_le, choose_zero_right, Finset.prod_const_one]

theorem uniformBell_mul_eq (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * n ! ^ m * m ! = (m * n)! := by
  convert! bell_mul_eq (replicate m n)
  · simp only [map_replicate, prod_replicate]
  · simp only [toFinset_replicate]
    split_ifs with hm
    · rw [hm, factorial_zero, eq_comm]
      rw [show (∅ : Finset ℕ).erase 0 = ∅ from rfl, Finset.prod_empty]
    · rw [show ({n} : Finset ℕ).erase 0 = {n} by simp [Ne.symm hn]]
      simp only [Finset.prod_singleton, count_replicate_self]
  · simp

theorem uniformBell_eq_div (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n = (m * n)! / (n ! ^ m * m !) := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_left
  · exact Nat.mul_pos (Nat.pow_pos n.factorial_pos) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

/--
The `n`th standard Bell number,
which counts the number of partitions of a set of cardinality `n`.
-/
protected def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i ≤ n, choose n i * (n - i).bell

theorem bell_succ (n : ℕ) :
    (n + 1).bell = ∑ i ≤ n, choose n i * (n - i).bell := by
  rw [Nat.bell]

theorem bell_succ' (n : ℕ) :
    (n + 1).bell = ∑ ij ∈ Finset.antidiagonal n, choose n ij.1 * ij.2.bell := by
  rw [Nat.bell_succ,
    ← Nat.range_succ_eq_Iic,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y ↦ choose n x * y.bell) n]

@[simp]
theorem bell_zero : Nat.bell 0 = 1 := by
  simp [Nat.bell]

@[simp]
theorem bell_one : Nat.bell 1 = 1 := by
  have : Finset.Iic 0 = {0} := Eq.symm (Finset.eq_of_veq rfl)
  simp [Nat.bell, this]

@[simp]
theorem bell_two : Nat.bell 2 = 2 := by
  have : Finset.Iic 1 = {0, 1} := Finset.eq_of_veq rfl
  simp [Nat.bell, this]

theorem bell_eq_sum_erase {n : ℕ} (p : (n + 1).Partition) :
    ∑ a ∈ p.parts.toFinset, n.choose (a - 1) * (p.parts.erase a).bell = p.parts.bell := by
  apply Nat.eq_of_mul_eq_mul_left n.succ_pos
  calc
  _ = ∑ a ∈ p.parts.toFinset, (n + 1) * (n.choose (a - 1) * (p.parts.erase a).bell) := by
    rw [Finset.mul_sum]
  _ = ∑ a ∈ p.parts.toFinset, a * (p.parts.count a * p.parts.bell) := by
    congr! 1 with a ha
    have ha_mem : a ∈ p.parts := mem_dedup.mp ha
    have ha0 : a ≠ 0 := by grind
    have hsum : (p.parts.erase a).sum + a = n + 1 := by
      simpa [p.parts_sum, add_comm] using congrArg Multiset.sum (Multiset.cons_erase ha_mem)
    have hbell : (n + 1).choose a * (p.parts.erase a).bell = p.parts.count a * p.parts.bell := by
      simpa [hsum, cons_erase ha_mem, mul_comm] using
        ((p.parts.erase a).bell_cons_mul_count ha0).symm
    calc
      _ = (n + 1) * n.choose (a - 1) * (p.parts.erase a).bell := by ring
      _ = _ := by grind [Nat.add_one_mul_choose_eq]
  _ = (∑ a ∈ p.parts.toFinset, p.parts.count a * a) * p.parts.bell := by grind [Finset.sum_mul]
  _ = _ := by
    rw [succ_eq_add_one, mul_eq_mul_right_iff]
    left
    simpa [smul_eq_mul, p.parts_sum] using (Finset.sum_multiset_count p.parts).symm

private def partitionWithPartEquiv {n a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ n) :
    {p : n.Partition // a ∈ p.parts} ≃ (n - a).Partition where
  toFun p := by
    refine ⟨p.1.parts.erase a, ?_, ?_⟩
    · intro _ hi
      exact p.1.parts_pos (p.1.parts.erase_subset a hi)
    · cases n
      · lia
      have hs : a + (p.1.parts.erase a).sum = n + 1 := by
        simpa [p.1.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase p.2)
      lia
  invFun q := ⟨⟨a ::ₘ q.parts, by grind, by simp [q.parts_sum, ha]⟩, by simp⟩
  left_inv p := Subtype.ext <| Partition.ext <| cons_erase p.property
  right_inv q := Partition.ext <| erase_cons_head a q.parts

private def sigmaPartitionWithPartEquiv (n : ℕ) :
    (Σ i : Fin n.succ, {p : (n + 1).Partition // (i + 1 : ℕ) ∈ p.parts}) ≃
    Σ p : (n + 1).Partition, {a : ℕ // a ∈ p.parts.toFinset} where
  toFun x := ⟨x.2.1, ⟨(x.1 + 1 : ℕ), by simpa using x.2.2⟩⟩
  invFun x := ⟨⟨x.2.1 - 1, by grind⟩, ⟨x.1, by grind⟩⟩
  left_inv x := by simp
  right_inv x := by grind

/-- `Nat.bell n` is equal to the sum of `Multiset.bell m` over all multisets `m : Multiset ℕ` such
that `m.sum = n`. -/
theorem bell_eq_sum_partition (n : ℕ) : n.bell = ∑ p : n.Partition, p.parts.bell := by
  refine Nat.strong_induction_on n ?_
  rintro (_ | n) ih
  · simp
  rw [Nat.bell_succ]
  calc
  _ = ∑ i ≤ n, ∑ q : (n - i).Partition, n.choose i * q.parts.bell := by
    congr! with i
    simp [ih (n - i) _, Finset.mul_sum]
  _ = ∑ i ≤ n, ∑ p : {p : (n + 1).Partition // (i + 1 : ℕ) ∈ p.parts},
      choose n i * (p.1.parts.erase (i + 1)).bell := by
    congr! with i hi
    have : i ≤ n := Finset.mem_Iic.mp hi
    have h1 : 1 ≤ (i + 1 : ℕ) := by lia
    have h2 : (i + 1 : ℕ) ≤ n + 1 := by lia
    have hsub : n + 1 - (i + 1 : ℕ) = n - i := by lia
    exact hsub ▸ (Fintype.sum_equiv (partitionWithPartEquiv h1 h2) _ _ (fun _ ↦ rfl)).symm
  _ = ∑ x : Σ p : (n + 1).Partition, p.parts.toFinset,
      choose n (x.2.1 - 1) * (x.1.parts.erase x.2.1).bell := by
    rw [← Nat.range_succ_eq_Iic, Finset.sum_range, ← Fintype.sum_sigma']
    refine Fintype.sum_equiv (sigmaPartitionWithPartEquiv n) _ _ ?_
    simp [sigmaPartitionWithPartEquiv]
  _ = ∑ p : (n + 1).Partition, ∑ a : p.parts.toFinset,
      choose n (a - 1) * (p.parts.erase a).bell :=
    Fintype.sum_sigma' fun (p : (n + 1).Partition) (a : p.parts.toFinset) ↦
      choose n (a - 1) * (p.parts.erase a.1).bell
  _ = _ := by
    congr! with p
    rw [← bell_eq_sum_erase p]
    exact p.parts.toFinset.sum_coe_sort (fun a ↦ choose n (a - 1) * (p.parts.erase a).bell)

end Nat
