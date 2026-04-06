/-
Copyright (c) 2024 Antoine Chambert-Loir & María-Inés de Frutos—Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos—Fernández, Yu Shao, Beibei Xiong, Weijie Jiang
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
    m.bell * (m.map (fun j ↦ j !)).prod * ∏ j ∈ (m.toFinset.erase 0), (m.count j)!
      = m.sum ! := by
  unfold bell
  rw [← Nat.mul_right_inj (a := ∏ i ∈ m.toFinset, (i * count i m)!) (by positivity)]
  simp only [← mul_assoc]
  rw [Nat.multinomial_spec]
  simp only [mul_assoc]
  rw [mul_comm]
  apply congr_arg₂
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
    apply Finset.prod_congr rfl
    intro x hx
    rw [← mul_assoc, bell_mul_eq_lemma]
    simp only [Finset.mem_erase, ne_eq, mem_toFinset] at hx
    simp only [ne_eq, hx.1, not_false_eq_true]
  · apply congr_arg
    rw [Finset.sum_multiset_count]
    simp only [smul_eq_mul, mul_comm]

theorem bell_eq (m : Multiset ℕ) :
    m.bell = m.sum ! / ((m.map (fun j ↦ j !)).prod *
      ∏ j ∈ (m.toFinset.erase 0), (m.count j)!) := by
  rw [← Nat.mul_left_inj, Nat.div_mul_cancel _]
  · rw [← mul_assoc]
    exact bell_mul_eq m
  · rw [← bell_mul_eq, mul_assoc]
    apply Nat.dvd_mul_left
  · rw [← Nat.pos_iff_ne_zero]
    apply Nat.mul_pos
    · simp only [CanonicallyOrderedAdd.multiset_prod_pos, mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact fun _ _ ↦ Nat.factorial_pos _
    · apply Finset.prod_pos
      exact fun _ _ ↦ Nat.factorial_pos _

theorem prod_count_factorial_eq_count_factorial_mul_prod_erase
    {m : Multiset ℕ} {a : ℕ} (ha : a ≠ 0) :
    ∏ j ∈ m.toFinset.erase 0, (m.count j)! =
      (m.count a)! * ∏ j ∈ (m.toFinset.erase 0).erase a, (m.count j)! := by
  by_cases hmem : a ∈ m.toFinset.erase 0
  · rw [← Finset.mul_prod_erase _ _ hmem]
  · rw [Finset.erase_eq_of_notMem hmem]
    have hcount : m.count a = 0 := by
      apply Multiset.count_eq_zero_of_notMem
      intro hm
      exact hmem <| by simpa [ha] using hm
    simp [hcount]

theorem prod_count_factorial_cons_erase {m : Multiset ℕ} {a : ℕ} :
    ∏ j ∈ ((a ::ₘ m).toFinset.erase 0).erase a, ((a ::ₘ m).count j)! =
    ∏ j ∈ (m.toFinset.erase 0).erase a, (m.count j)! := by
  have hset : ((a ::ₘ m).toFinset.erase 0).erase a = (m.toFinset.erase 0).erase a := by
    ext x
    by_cases hx : x = a
    · simp [hx]
    · simp [Multiset.toFinset_cons, hx]
  rw [hset]
  refine Finset.prod_congr rfl ?_
  intro j hj
  simp [(Finset.mem_erase.mp hj).1]

theorem map_factorial_prod_pos (m : Multiset ℕ) : 0 < (m.map (fun j ↦ j !)).prod := by
  simpa only [CanonicallyOrderedAdd.multiset_prod_pos, mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] using fun _ _ ↦ Nat.factorial_pos _

theorem bell_cons_mul_count {m : Multiset ℕ} {a : ℕ} (ha : a ≠ 0) :
    (a ::ₘ m).bell * (a ::ₘ m).count a = Nat.choose (m.sum + a) a * m.bell := by
  let rest := ∏ j ∈ (m.toFinset.erase 0).erase a, (m.count j)!
  let c := a ! * ((m.map (fun j ↦ j !)).prod * ((m.count a)! * rest))
  have hm0 : m.bell * ((m.map (fun j ↦ j !)).prod * ((m.count a)! * rest)) = m.sum ! := by
    have hm := Multiset.bell_mul_eq m
    rw [prod_count_factorial_eq_count_factorial_mul_prod_erase (a := a) ha] at hm
    simpa [rest, mul_assoc, mul_comm, mul_left_comm] using hm
  have hm : m.bell * c = m.sum ! * a ! := by
    simpa [c, mul_assoc, mul_comm, mul_left_comm] using congrArg (fun t => a ! * t) hm0
  have ha_mem : a ∈ (a ::ₘ m).toFinset.erase 0 := by
    simp [ha]
  have hc : 0 < c := Nat.mul_pos (Nat.factorial_pos _) <|
      Nat.mul_pos (map_factorial_prod_pos m) <| by positivity
  apply Nat.eq_of_mul_eq_mul_right hc
  calc
    _ = (a ::ₘ m).bell * ((m.count a + 1) * c) := by
      simp [mul_assoc]
    _ = (m.sum + a)! := by
      have hq := Multiset.bell_mul_eq (a ::ₘ m)
      rw [← Finset.mul_prod_erase _ _ ha_mem, prod_count_factorial_cons_erase] at hq
      simpa [c, rest, Nat.factorial_succ, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
        add_comm, mul_assoc, mul_comm, mul_left_comm] using hq
    _ = Nat.choose (m.sum + a) a * (m.sum ! * a !) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial]
      ring
    _ = Nat.choose (m.sum + a) a * (m.bell * c) := by rw [hm]
    _ = (Nat.choose (m.sum + a) a * m.bell) * c := by
      simp [mul_assoc, mul_comm, mul_left_comm]

end Multiset

namespace Nat

/-- Number of possibilities of dividing a set with `m * n` elements into `m` groups
of `n`-element subsets. -/
def uniformBell (m n : ℕ) : ℕ := bell (replicate m n)

theorem uniformBell_eq (m n : ℕ) : m.uniformBell n =
    ∏ p ∈ (Finset.range m), Nat.choose (p * n + n - 1) (n - 1) := by
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
  convert bell_mul_eq (replicate m n)
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
  · exact Nat.mul_pos (Nat.pow_pos (Nat.factorial_pos n)) m.factorial_pos
  · rw [← mul_assoc, ← uniformBell_mul_eq _ hn]

/--
The `n`th standard Bell number,
which counts the number of partitions of a set of cardinality `n`.

## TODO

Prove that `Nat.bell n` is equal to the sum of `Multiset.bell m`
over all multisets `m : Multiset ℕ` such that `m.sum = n`.
-/
protected def bell : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin n.succ, choose n i * Nat.bell (n - i)

theorem bell_succ (n : ℕ) :
    Nat.bell (n + 1) = ∑ i : Fin n.succ, Nat.choose n i * Nat.bell (n - i) := by
  rw [Nat.bell]

theorem bell_succ' (n : ℕ) :
    Nat.bell (n + 1) = ∑ ij ∈ Finset.antidiagonal n, Nat.choose n ij.1 * Nat.bell ij.2 := by
  rw [Nat.bell_succ,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => Nat.choose n x * Nat.bell y) n,
    Finset.sum_range]


@[simp]
theorem bell_zero : Nat.bell 0 = 1 := by
  simp [Nat.bell]

@[simp]
theorem bell_one : Nat.bell 1 = 1 := by
  simp [Nat.bell]

@[simp]
theorem bell_two : Nat.bell 2 = 2 := by
  simp [Nat.bell]

private theorem bell_eq_sum_erase {n : ℕ} (p : Nat.Partition (n + 1)) :
    ∑ a ∈ p.parts.toFinset, Nat.choose n (a - 1) * Multiset.bell (p.parts.erase a) =
      Multiset.bell p.parts := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n)
  calc
    _ = ∑ a ∈ p.parts.toFinset,
        (n + 1) * (Nat.choose n (a - 1) * Multiset.bell (p.parts.erase a)) := by
      rw [Finset.mul_sum]
    _ = ∑ a ∈ p.parts.toFinset, a * (p.parts.count a * Multiset.bell p.parts) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      have ha_mem : a ∈ p.parts := by simpa using ha
      have ha0 : a ≠ 0 := by
        intro h
        exact (p.parts_pos ha_mem).ne' h
      have hsum : (p.parts.erase a).sum + a = n + 1 := by
        simpa [p.parts_sum, add_comm] using congrArg Multiset.sum (Multiset.cons_erase ha_mem)
      have hbell :
          Nat.choose (n + 1) a * (p.parts.erase a).bell = p.parts.count a * p.parts.bell := by
        simpa [hsum, Multiset.cons_erase ha_mem, mul_comm, mul_left_comm, mul_assoc] using
          (Multiset.bell_cons_mul_count (m := p.parts.erase a) (a := a) ha0).symm
      calc
        (n + 1) * (Nat.choose n (a - 1) * Multiset.bell (p.parts.erase a))
            = ((n + 1) * Nat.choose n (a - 1)) * Multiset.bell (p.parts.erase a) := by ring
        _ = (Nat.choose (n + 1) a * a) * Multiset.bell (p.parts.erase a) := by
              have ha1 : 1 ≤ a := Nat.succ_le_of_lt (p.parts_pos ha_mem)
              rw [Nat.add_one_mul_choose_eq, Nat.sub_add_cancel ha1]
        _ = a * (Nat.choose (n + 1) a * Multiset.bell (p.parts.erase a)) := by ring
        _ = a * (p.parts.count a * Multiset.bell p.parts) := by rw [hbell]
    _ = (∑ a ∈ p.parts.toFinset, p.parts.count a * a) * Multiset.bell p.parts := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro a ha
      ring
    _ = (n + 1) * Multiset.bell p.parts := by
      have hsum : ∑ a ∈ p.parts.toFinset, p.parts.count a * a = n + 1 := by
        simpa [smul_eq_mul, p.parts_sum, mul_comm] using
          (Finset.sum_multiset_count (s := p.parts)).symm
      rw [hsum]

private def partitionWithPartEquiv {n a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ n + 1) :
    {p : Nat.Partition (n + 1) // a ∈ p.parts} ≃ Nat.Partition (n + 1 - a) where
  toFun p := by
    refine ⟨p.1.parts.erase a, ?_, ?_⟩
    · intro i hi
      exact p.1.parts_pos (Multiset.erase_subset a p.1.parts hi)
    · have hs : a + (p.1.parts.erase a).sum = n + 1 := by
        simpa [p.1.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase p.2)
      omega
  invFun q := by
    refine ⟨⟨a ::ₘ q.parts, ?_, ?_⟩, by simp⟩
    · intro i hi
      rw [Multiset.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ha1
      · exact q.parts_pos hi
    · simp [q.parts_sum, ha]
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change a ::ₘ p.1.parts.erase a = p.1.parts
    exact Multiset.cons_erase p.2
  right_inv q := by
    apply Nat.Partition.ext
    change (a ::ₘ q.parts).erase a = q.parts
    exact Multiset.erase_cons_head a q.parts

private def partitionPartEquiv (n : ℕ) :
    (Σ p : Nat.Partition (n + 1), {a // a ∈ p.parts.toFinset}) ≃
      Σ a : {a : ℕ // a ∈ Finset.Icc 1 (n + 1)}, Nat.Partition (n + 1 - a) where
  toFun x := by
    let a : ℕ := x.2
    have ha_mem : a ∈ x.1.parts := by
      dsimp [a]
      exact Multiset.mem_toFinset.mp x.2.2
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt (x.1.parts_pos ha_mem)
    have ha_le : a ≤ n + 1 := Nat.Partition.le_of_mem_parts ha_mem
    exact ⟨⟨a, by simp [ha1, ha_le]⟩, partitionWithPartEquiv ha1 ha_le ⟨x.1, ha_mem⟩⟩
  invFun x := by
    rcases x with ⟨⟨a, ha⟩, q⟩
    simp only [Finset.mem_Icc] at ha
    let p : Nat.Partition (n + 1) := (partitionWithPartEquiv ha.1 ha.2).symm q
    refine ⟨p, ⟨a, by simpa using ((partitionWithPartEquiv ha.1 ha.2).symm q).2⟩⟩
  left_inv x := by
    rcases x with ⟨p, ⟨a, ha⟩⟩
    have ha_mem : a ∈ p.parts := Multiset.mem_toFinset.mp ha
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt (p.parts_pos ha_mem)
    have ha_le : a ≤ n + 1 := Nat.Partition.le_of_mem_parts ha_mem
    simpa using congrArg
      (fun y : {p : Nat.Partition (n + 1) // a ∈ p.parts} =>
        (⟨y.1, ⟨a, by simpa using y.2⟩⟩ :
          Σ p : Nat.Partition (n + 1), {a // a ∈ p.parts.toFinset}))
      ((partitionWithPartEquiv ha1 ha_le).left_inv ⟨p, ha_mem⟩)
  right_inv x := by
    rcases x with ⟨⟨a, ha⟩, q⟩
    simp only [Finset.mem_Icc] at ha
    simpa only using
      congrArg
        (fun q : Nat.Partition (n + 1 - a) =>
          (⟨⟨a, by simpa only⟩, q⟩ :
            Σ a : { a : ℕ // a ∈ Finset.Icc 1 (n + 1) }, Nat.Partition (n + 1 - a)))
        ((partitionWithPartEquiv ha.1 ha.2).right_inv q)

private def finSuccEquivIcc (n : ℕ) :
    Fin n.succ ≃ {a : ℕ // a ∈ Finset.Icc 1 (n + 1)} where
  toFun i := ⟨i + 1, by
    simp [Finset.mem_Icc, Nat.le_of_lt_succ i.is_lt]⟩
  invFun a := ⟨a - 1, by
    rcases a with ⟨a, ha⟩
    simp only [Finset.mem_Icc] at ha
    have hle : a - 1 + 1 ≤ n + 1 := by simpa [Nat.sub_add_cancel ha.1] using ha.2
    exact lt_of_lt_of_le (Nat.lt_succ_self (a - 1)) hle⟩
  left_inv i := by
    ext
    exact Nat.add_sub_cancel_right i 1
  right_inv a := by
    rcases a with ⟨a, ha⟩
    ext
    simp only [Finset.mem_Icc] at ha
    exact Nat.sub_add_cancel ha.1

private def finPartitionEquiv (n : ℕ) :
    (Σ a : {a : ℕ // a ∈ Finset.Icc 1 (n + 1)}, Nat.Partition (n + 1 - a)) ≃
      Σ i : Fin n.succ, Nat.Partition (n - i) :=
  (Equiv.sigmaCongrLeft' (finSuccEquivIcc n).symm).trans <|
    Equiv.sigmaCongrRight fun i =>
      Equiv.cast <| by
        simp [finSuccEquivIcc]

private theorem bell_parts_cast_symm {m n : ℕ} (h : m = n) (p : Nat.Partition n) :
    Multiset.bell (((Equiv.cast (congrArg Nat.Partition h)).symm p).parts) = Multiset.bell p.parts := by
  cases h
  rfl

theorem bell_eq_sum_partition (n : ℕ) :
    Nat.bell n = ∑ p : Nat.Partition n, Multiset.bell p.parts := by
  classical
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero => simp
  | succ n =>
      symm
      calc
        _ = ∑ p : Nat.Partition (n + 1),
                ∑ a ∈ p.parts.toFinset, Nat.choose n (a - 1) * Multiset.bell (p.parts.erase a) := by
              congr with p
              exact (bell_eq_sum_erase p).symm
        _ = ∑ p : Nat.Partition (n + 1),
                ∑ a : {a // a ∈ p.parts.toFinset},
                  Nat.choose n (a - 1) * Multiset.bell (p.parts.erase a) := by
              congr with p
              rw [← Finset.sum_coe_sort]
        _ = ∑ x : Σ p : Nat.Partition (n + 1), {a // a ∈ p.parts.toFinset},
                Nat.choose n (x.2 - 1) * Multiset.bell (x.1.parts.erase x.2) := by
              simpa using
                (Fintype.sum_sigma'
                  (fun p : Nat.Partition (n + 1) =>
                    fun a : {a // a ∈ p.parts.toFinset} =>
                      Nat.choose n ((a : ℕ) - 1) * Multiset.bell (p.parts.erase a))).symm
        _ = ∑ y : Σ a : {a : ℕ // a ∈ Finset.Icc 1 (n + 1)}, Nat.Partition (n + 1 - a),
                Nat.choose n (y.1 - 1) * Multiset.bell y.2.parts := by
              exact Fintype.sum_equiv (partitionPartEquiv n)
                (fun x => Nat.choose n (x.2 - 1) * Multiset.bell (x.1.parts.erase x.2))
                (fun y => Nat.choose n (y.1 - 1) * Multiset.bell y.2.parts) (by
                  intro x
                  dsimp [partitionPartEquiv, partitionWithPartEquiv])
        _ = ∑ z : Σ i : Fin n.succ, Nat.Partition (n - i),
                (fun y : Σ a : {a : ℕ // a ∈ Finset.Icc 1 (n + 1)}, Nat.Partition (n + 1 - a) =>
                  Nat.choose n (y.1 - 1) * Multiset.bell y.2.parts) ((finPartitionEquiv n).symm z) := by
              symm
              exact ((finPartitionEquiv n).symm).sum_comp
                (fun y : Σ a : {a : ℕ // a ∈ Finset.Icc 1 (n + 1)}, Nat.Partition (n + 1 - a) =>
                  Nat.choose n (y.1 - 1) * Multiset.bell y.2.parts)
        _ = ∑ z : Σ i : Fin n.succ, Nat.Partition (n - i),
                Nat.choose n z.1 * Multiset.bell z.2.parts := by
              congr with z
              rcases z with ⟨i, q⟩
              dsimp [finPartitionEquiv, finSuccEquivIcc, Equiv.sigmaCongrLeft', Equiv.sigmaCongrLeft,
                Equiv.sigmaCongrRight]
              rw [bell_parts_cast_symm (p := q)]
              simp
        _ = ∑ i : Fin n.succ, ∑ q : Nat.Partition (n - i), Nat.choose n i * Multiset.bell q.parts := by
              simpa using
                (Fintype.sum_sigma'
                  (fun i : Fin n.succ =>
                    fun q : Nat.Partition (n - i) =>
                      Nat.choose n i * Multiset.bell q.parts))
        _ = ∑ i : Fin n.succ, Nat.choose n i * ∑ q : Nat.Partition (n - i), Multiset.bell q.parts := by
              congr with i
              rw [← Finset.mul_sum]
        _ = ∑ i : Fin n.succ, Nat.choose n i * Nat.bell (n - i) := by
              congr with i
              rw [ih (n - i) (Nat.lt_succ_of_le (Nat.sub_le _ _))]
        _ = Nat.bell (n + 1) := by rw [Nat.bell_succ]

end Nat
