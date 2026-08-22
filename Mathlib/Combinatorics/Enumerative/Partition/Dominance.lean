/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.YoungDiagram

/-!
# The dominance order on partitions

This file defines dominance of partitions of a fixed natural number: `μ.Dominates ν` means that
every prefix sum of the decreasingly sorted parts of `μ` is at least the corresponding prefix
sum for `ν`. Dominance is the triangular order governing Kostka numbers and the occurrence of
Specht modules in permutation modules.

## Main definitions

* `Nat.Partition.Dominates`: the dominance relation, with the orientation that `μ.Dominates ν`
  means "`μ` dominates `ν`".

## Main results

* `Nat.Partition.Dominates.refl`, `Nat.Partition.Dominates.trans`, and
  `Nat.Partition.Dominates.antisymm`: dominance is reflexive, transitive, and antisymmetric.
* `Nat.Partition.indiscrete_dominates`: the one-part partition dominates every partition;
  `Nat.Partition.dominates_indiscrete_iff` says that it is dominated only by itself.
* `Nat.Partition.conjugate_dominates_conjugate_iff`: conjugation reverses dominance.

The dominance *order instance* on `Nat.Partition n` is deliberately not installed here: it would
have to choose between the two possible orientations of `≤`, and downstream applications may
reasonably want either. Statements use the named relation instead.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], §1.1

## Tags

partition, dominance, dominance order, conjugate partition
-/

@[expose] public section

open scoped Finset

/-!
### Prefix-sum lemmas for lists of naturals

These private lemmas compare prefix sums of weakly decreasing lists of naturals. They are the
combinatorial engine behind antisymmetry of dominance and its reversal under conjugation.
-/

/-- For a weakly decreasing list, subtracting `k` from every entry and adding back `k` for each
entry exceeding `k` recovers the prefix sum over the entries exceeding `k`. -/
private theorem sum_sub_add_mul_length_takeWhile {l : List ℕ} (hl : l.SortedGE) (k : ℕ) :
    (l.map fun x => x - k).sum + k * (l.takeWhile fun x => decide (k < x)).length =
      (l.takeWhile fun x => decide (k < x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hlsorted : l.SortedGE := hl.pairwise.tail.sortedGE
    by_cases ha : k < a
    · rw [List.takeWhile_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have htail := ih hlsorted
      rw [Nat.mul_succ]
      omega
    · have hale : a ≤ k := Nat.le_of_not_gt ha
      have htail : ∀ x ∈ l, x ≤ k := fun x hx =>
        (hl.pairwise.rel_head_tail (by simpa using hx)).trans hale
      have hsum : (l.map fun x => x - k).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact Nat.sub_eq_zero_of_le (htail x hx)
      rw [List.takeWhile_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.sum_cons, List.sum_nil, List.length_nil, mul_zero,
        add_zero, Nat.sub_eq_zero_of_le hale]
      simpa only [zero_add] using hsum

private theorem sum_take_le_mul_add_sum_sub (l : List ℕ) (k r : ℕ) :
    (l.take r).sum ≤ k * r + (l.map fun x => x - k).sum := by
  induction r generalizing l with
  | zero => simp
  | succ r ih =>
    cases l with
    | nil => simp
    | cons a l =>
      simp only [List.take_succ_cons, List.sum_cons, List.map_cons, Nat.mul_succ]
      have htail := ih l
      omega

private theorem sum_min_add_sum_sub (l : List ℕ) (k : ℕ) :
    (l.map (min k)).sum + (l.map fun x => x - k).sum = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [← ih]
    omega

/-- Domination of prefix sums is reversed, entrywise truncated at any level `k`, on lists of
equal sum. This is the key step in showing that conjugation reverses dominance, since truncated
sums of row lengths are prefix sums of column lengths. -/
private theorem sum_map_min_le_of_prefix_sum_le {l₁ l₂ : List ℕ}
    (hl₂ : l₂.SortedGE) (hsum : l₁.sum = l₂.sum)
    (hle : ∀ r, (l₂.take r).sum ≤ (l₁.take r).sum) (k : ℕ) :
    (l₁.map (min k)).sum ≤ (l₂.map (min k)).sum := by
  let r := (l₂.takeWhile fun x => decide (k < x)).length
  have htake : l₂.take r = l₂.takeWhile fun x => decide (k < x) :=
    (List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)).symm
  have hexcess : (l₂.map fun x => x - k).sum + k * r = (l₂.take r).sum := by
    rw [htake]
    exact sum_sub_add_mul_length_takeWhile hl₂ k
  have hsub : (l₂.map fun x => x - k).sum ≤ (l₁.map fun x => x - k).sum := by
    have hpref := hle r
    have hupper := sum_take_le_mul_add_sum_sub l₁ k r
    omega
  have hsplit₁ := sum_min_add_sum_sub l₁ k
  have hsplit₂ := sum_min_add_sum_sub l₂ k
  omega

/-- If two different lists of positive naturals have equal sums and the prefix sums of `l₁`
dominate those of `l₂`, then `l₂` strictly precedes `l₁` lexicographically. -/
private theorem lex_lt_of_prefix_sum_le {l₁ l₂ : List ℕ}
    (hsum : l₁.sum = l₂.sum)
    (hpos₁ : ∀ i ∈ l₁, 0 < i) (hpos₂ : ∀ i ∈ l₂, 0 < i)
    (hle : ∀ k : ℕ, (l₂.take k).sum ≤ (l₁.take k).sum)
    (hne : l₁ ≠ l₂) : l₂ < l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact (hne rfl).elim
    | cons b l₂ =>
      have hb : 0 < b := hpos₂ b (by simp)
      simp only [List.sum_nil, List.sum_cons] at hsum
      omega
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      have ha : 0 < a := hpos₁ a (by simp)
      simp only [List.sum_cons, List.sum_nil] at hsum
      omega
    | cons b l₂ =>
      have hba : b ≤ a := by
        simpa only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil,
          add_zero] using hle 1
      rcases hba.eq_or_lt with hba | hba
      · subst b
        apply List.Lex.cons
        apply ih
        · simpa only [List.sum_cons, Nat.add_left_cancel_iff] using hsum
        · intro i hi
          exact hpos₁ i (by simp [hi])
        · intro i hi
          exact hpos₂ i (by simp [hi])
        · intro k
          simpa only [List.take_succ_cons, List.sum_cons, Nat.add_le_add_iff_left] using
            hle (k + 1)
        · intro h
          exact hne (congrArg (List.cons a) h)
      · exact List.Lex.rel hba

/-!
### Truncated sums of row lengths and transposition

Truncating the row lengths of a Young diagram at `k` and summing counts the cells in the first
`k` columns, which is the `k`-th prefix sum of the row lengths of the transposed diagram.
-/

private theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = #{c ∈ μ.cells | c.1 < k} := by
  rw [YoungDiagram.rowLens, ← List.map_take, List.take_range,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  symm
  calc
    #{c ∈ μ.cells | c.1 < k} =
        ∑ i ∈ Finset.range (min k (μ.colLen 0)), #{c ∈ {c ∈ μ.cells | c.1 < k} | c.1 = i} := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
      rw [Finset.mem_range]
      refine lt_min hc.2 ?_
      rw [← YoungDiagram.mem_iff_lt_colLen]
      exact μ.up_left_mem (by rfl) c.2.zero_le hc.1
    _ = ∑ i ∈ Finset.range (min k (μ.colLen 0)), μ.rowLen i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := (Finset.mem_range.mp hi).trans_le (min_le_left _ _)
      simp only [Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_row_iff]
      aesop

private theorem sum_map_min_rowLens_eq_card_filter_snd (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.map (min k)).sum = #{c ∈ μ.cells | c.2 < k} := by
  rw [YoungDiagram.rowLens, List.map_map,
    ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  symm
  calc
    #{c ∈ μ.cells | c.2 < k} =
        ∑ i ∈ Finset.range (μ.colLen 0), #{c ∈ {c ∈ μ.cells | c.2 < k} | c.1 = i} := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc ⊢
      rw [Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen]
      exact μ.up_left_mem (by rfl) c.2.zero_le hc.1
    _ = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hfiber : {c ∈ {c ∈ μ.cells | c.2 < k} | c.1 = i} =
          {i} ×ˢ Finset.range (min k (μ.rowLen i)) := by
        ext c
        simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product,
          Finset.mem_singleton, Finset.mem_range, lt_min_iff]
        rw [YoungDiagram.mem_iff_lt_rowLen]
        aesop
      rw [hfiber, Finset.card_product]
      simp

private theorem card_filter_fst_transpose (μ : YoungDiagram) (k : ℕ) :
    #{c ∈ μ.transpose.cells | c.1 < k} = #{c ∈ μ.cells | c.2 < k} := by
  apply Finset.card_equiv (Equiv.prodComm ℕ ℕ)
  intro c
  simp

/-- Prefix sums of the row lengths of the transpose are truncated sums of the row lengths. -/
private theorem sum_take_transpose_rowLens (μ : YoungDiagram) (k : ℕ) :
    (μ.transpose.rowLens.take k).sum = (μ.rowLens.map (min k)).sum := by
  rw [sum_take_rowLens_eq_card_filter_fst, card_filter_fst_transpose,
    sum_map_min_rowLens_eq_card_filter_snd]

namespace Nat.Partition

variable {n : ℕ} {μ ν ξ : Partition n}

private theorem sum_sort_parts (μ : Partition n) : (μ.parts.sort (· ≥ ·)).sum = n := by
  rw [← Multiset.sum_coe, Multiset.sort_eq]
  exact μ.parts_sum

private theorem length_sort_parts_le (μ : Partition n) : (μ.parts.sort (· ≥ ·)).length ≤ n :=
  le_of_le_of_eq
    (List.length_le_sum_of_one_le _ fun _ hi => μ.parts_pos ((Multiset.mem_sort _).mp hi))
    (sum_sort_parts μ)

/-- A partition `μ` of `n` *dominates* a partition `ν` of `n` when every prefix sum of the
decreasingly sorted parts of `μ` is at least the corresponding prefix sum for `ν`.

`μ.Dominates ν` is to be read as "`μ` dominates `ν`"; for example, the one-part partition
dominates every partition of `n` (`Nat.Partition.indiscrete_dominates`). No order instance is
installed for this relation; see the module docstring. -/
def Dominates (μ ν : Partition n) : Prop :=
  ∀ k : ℕ, ((ν.parts.sort (· ≥ ·)).take k).sum ≤ ((μ.parts.sort (· ≥ ·)).take k).sum

/-- Prefix sums of sorted parts of partitions of `n` agree from index `n` on, so dominance is
determined by the first `n + 1` prefix sums. In particular it is decidable. -/
theorem dominates_iff_forall_fin :
    μ.Dominates ν ↔ ∀ k : Fin (n + 1),
      ((ν.parts.sort (· ≥ ·)).take k).sum ≤ ((μ.parts.sort (· ≥ ·)).take k).sum := by
  refine ⟨fun h k => h k, fun h k => ?_⟩
  rcases le_or_gt k n with hk | hk
  · exact h ⟨k, Nat.lt_succ_iff.mpr hk⟩
  · rw [List.take_of_length_le ((length_sort_parts_le ν).trans hk.le),
      List.take_of_length_le ((length_sort_parts_le μ).trans hk.le),
      sum_sort_parts, sum_sort_parts]

instance (μ ν : Partition n) : Decidable (μ.Dominates ν) :=
  decidable_of_iff _ dominates_iff_forall_fin.symm

/-- Every partition dominates itself. -/
@[refl, simp]
protected theorem Dominates.refl (μ : Partition n) : μ.Dominates μ := fun _ => le_rfl

/-- Dominance is transitive. -/
protected theorem Dominates.trans (hμν : μ.Dominates ν) (hνξ : ν.Dominates ξ) :
    μ.Dominates ξ :=
  fun k => (hνξ k).trans (hμν k)

private theorem lex_lt_of_dominates_of_ne (hdom : μ.Dominates ν) (hne : μ ≠ ν) :
    ν.parts.sort (· ≥ ·) < μ.parts.sort (· ≥ ·) := by
  apply lex_lt_of_prefix_sum_le ((sum_sort_parts μ).trans (sum_sort_parts ν).symm)
  · exact fun i hi => μ.parts_pos ((Multiset.mem_sort _).mp hi)
  · exact fun i hi => ν.parts_pos ((Multiset.mem_sort _).mp hi)
  · exact hdom
  · intro h
    apply hne
    ext1
    rw [← Multiset.sort_eq μ.parts (· ≥ ·), ← Multiset.sort_eq ν.parts (· ≥ ·), h]

/-- Dominance is antisymmetric. -/
protected theorem Dominates.antisymm (hμν : μ.Dominates ν) (hνμ : ν.Dominates μ) : μ = ν := by
  by_contra hne
  exact (lex_lt_of_dominates_of_ne hμν hne).asymm (lex_lt_of_dominates_of_ne hνμ (Ne.symm hne))

instance : Trans (α := Partition n) (β := Partition n) (γ := Partition n)
    Dominates Dominates Dominates := ⟨Dominates.trans⟩

/-- The one-part partition dominates every partition of the same natural number. -/
@[simp]
theorem indiscrete_dominates (μ : Partition n) : (indiscrete n).Dominates μ := by
  intro k
  rcases k with _ | k
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [indiscrete_parts hn]
  simp only [Multiset.sort_singleton, List.take_succ_cons, List.sum_cons]
  have hsplit := congrArg List.sum (List.take_append_drop (k + 1) (μ.parts.sort (· ≥ ·)))
  rw [List.sum_append, sum_sort_parts] at hsplit
  omega

/-- A partition dominates the one-part partition only when it is that partition. -/
@[simp]
theorem dominates_indiscrete_iff : μ.Dominates (indiscrete n) ↔ μ = indiscrete n :=
  ⟨fun h => h.antisymm (indiscrete_dominates μ), fun h => h ▸ Dominates.refl μ⟩

/-!
### Conjugation reverses dominance
-/

private theorem sort_parts_conjugate (μ : Partition n) :
    μ.conjugate.parts.sort (· ≥ ·) = (YoungDiagram.ofPartition μ).transpose.rowLens := by
  simp only [conjugate, YoungDiagram.toPartition, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ (YoungDiagram.ofPartition μ).transpose.rowLens_sorted.pairwise

/-- **Conjugation of partitions reverses dominance.** If `μ` dominates `ν`, then the conjugate
of `ν` dominates the conjugate of `μ`. -/
protected theorem Dominates.conjugate (h : μ.Dominates ν) :
    ν.conjugate.Dominates μ.conjugate := by
  intro k
  rw [sort_parts_conjugate, sort_parts_conjugate, sum_take_transpose_rowLens,
    sum_take_transpose_rowLens, YoungDiagram.rowLens_ofPartition_eq_sort_parts,
    YoungDiagram.rowLens_ofPartition_eq_sort_parts]
  apply sum_map_min_le_of_prefix_sum_le
  · exact (Multiset.pairwise_sort ν.parts (· ≥ ·)).sortedGE
  · exact (sum_sort_parts μ).trans (sum_sort_parts ν).symm
  · exact h

/-- **Conjugation of partitions reverses dominance**: `μ'` dominates `ν'` exactly when `ν`
dominates `μ`. -/
@[simp]
theorem conjugate_dominates_conjugate_iff :
    μ.conjugate.Dominates ν.conjugate ↔ ν.Dominates μ :=
  ⟨fun h => by simpa using h.conjugate, fun h => h.conjugate⟩

end Nat.Partition
