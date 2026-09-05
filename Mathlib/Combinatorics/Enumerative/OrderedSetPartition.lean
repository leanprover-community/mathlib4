/-
Copyright (c) 2026 Dennis Michael Heine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennis Michael Heine
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

/-! # Counting ordered partitions of a finite set

An *ordered partition* of a finset `A` with block sizes `c : Fin k → ℕ` is a family
`T : Fin k → Finset A` of pairwise disjoint blocks whose union is `A` and with
`(T i).card = c i`. This file counts them: there are `A.card ! / ∏ i, (c i)!` of them,
the multinomial coefficient.

`Mathlib` already knows the case `k = 2` in the guise of `Finset.card_powersetCard`;
the general statement is obtained from it by induction on the number of blocks.

## Main results

* `Finset.orderedPartitions`: the ordered partitions of `A` with prescribed block sizes.
* `Finset.card_orderedPartitions_mul_prod_factorial`: the multinomial count, in the
  division-free form `#(A.orderedPartitions c) * ∏ i, (c i)! = A.card !`.
* `Finset.card_orderedPartitions`: the same with a division.

## Implementation notes

Blocks are allowed to be empty, so `c` may take the value `0`; this costs nothing in the
proof and keeps the statement free of side conditions.
-/

@[expose] public section

open Nat

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- The ordered partitions of `A` into `k` blocks of prescribed sizes `c`: families of
pairwise disjoint blocks with union `A` and `#(T i) = c i`. -/
def orderedPartitions (A : Finset α) {k : ℕ} (c : Fin k → ℕ) :
    Finset (Fin k → Finset α) :=
  (Fintype.piFinset fun _ => A.powerset).filter fun T =>
    (∀ i, (T i).card = c i) ∧ (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧ univ.sup T = A

theorem mem_orderedPartitions {A : Finset α} {k : ℕ} {c : Fin k → ℕ}
    {T : Fin k → Finset α} :
    T ∈ A.orderedPartitions c ↔ (∀ i, T i ⊆ A) ∧ (∀ i, (T i).card = c i) ∧
      (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧ univ.sup T = A := by
  unfold orderedPartitions
  simp only [mem_filter, Fintype.mem_piFinset, mem_powerset]

/-- The union of a family indexed by `Fin (k + 1)`, split off at the first index. -/
theorem sup_univ_fin_succ {k : ℕ} (T : Fin (k + 1) → Finset α) :
    univ.sup T = T 0 ∪ univ.sup (Fin.tail T) := by
  ext x
  simp only [mem_union, mem_sup, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases ?_ ?_ i hi
    · exact fun h => Or.inl h
    · exact fun j h => Or.inr ⟨j, h⟩
  · rintro (h | ⟨j, hj⟩)
    · exact ⟨0, h⟩
    · exact ⟨j.succ, hj⟩

/-- Fixing the first block identifies the remaining ones with an ordered partition of the
complement. -/
theorem card_filter_orderedPartitions (A S : Finset α) {k : ℕ} (c : Fin (k + 1) → ℕ)
    (hS : S ⊆ A) (hcard : S.card = c 0) :
    ((A.orderedPartitions c).filter fun T => T 0 = S).card
      = ((A \ S).orderedPartitions (Fin.tail c)).card := by
  refine card_bij' (fun T _ => Fin.tail T) (fun U _ => Fin.cons S U) ?_ ?_ ?_ ?_
  · intro T hT
    rw [mem_filter, mem_orderedPartitions] at hT
    obtain ⟨⟨hsub, hcards, hdisj, hsup⟩, h0⟩ := hT
    have hnotS : ∀ (j : Fin k) {x : α}, x ∈ T j.succ → x ∉ S := by
      intro j x hx hxS
      exact disjoint_left.mp (hdisj j.succ 0 (Fin.succ_ne_zero j)) hx (h0 ▸ hxS)
    have hsplit : A = S ∪ univ.sup (Fin.tail T) := by
      rw [← hsup, sup_univ_fin_succ, h0]
    rw [mem_orderedPartitions]
    refine ⟨fun i x hx => mem_sdiff.mpr ⟨hsub _ hx, hnotS i hx⟩, fun i => hcards i.succ,
      fun i j hij => hdisj i.succ j.succ (by simpa using hij), ?_⟩
    ext x
    simp only [mem_sdiff]
    constructor
    · intro hx
      obtain ⟨j, -, hj⟩ := mem_sup.mp hx
      exact ⟨hsplit ▸ mem_union_right _ hx, hnotS j hj⟩
    · rintro ⟨hxA, hxS⟩
      rw [hsplit] at hxA
      exact (mem_union.mp hxA).resolve_left hxS
  · intro U hU
    rw [mem_orderedPartitions] at hU
    obtain ⟨hsub, hcards, hdisj, hsup⟩ := hU
    rw [mem_filter, mem_orderedPartitions]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, by simp⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hS
      · intro j
        simpa using (hsub j).trans sdiff_subset
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hcard
      · intro j; simpa [Fin.tail] using hcards j
    · intro i j
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · intro hij; exact absurd rfl hij
        · intro l _
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact disjoint_left.mpr fun x hx hxU => (mem_sdiff.mp (hsub l hxU)).2 hx
      · intro l
        refine Fin.cases ?_ ?_ j
        · intro _
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact disjoint_left.mpr fun x hx hxS => (mem_sdiff.mp (hsub l hx)).2 hxS
        · intro m hij
          simp only [Fin.cons_succ]
          exact hdisj l m (by simpa using hij)
    · rw [sup_univ_fin_succ, Fin.cons_zero, Fin.tail_cons, hsup, union_sdiff_of_subset hS]
  · intro T hT
    rw [mem_filter] at hT
    rw [← hT.2]
    exact Fin.cons_self_tail T
  · intro U _
    funext i
    simp [Fin.tail]

theorem orderedPartitions_of_isEmpty (c : Fin 0 → ℕ) :
    (∅ : Finset α).orderedPartitions c = {default} := by
  ext T
  rw [mem_singleton]
  refine ⟨fun _ => Subsingleton.elim _ _, ?_⟩
  rintro rfl
  rw [mem_orderedPartitions]
  exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- **The multinomial coefficient counts ordered partitions of a finset with prescribed
block sizes**, in division-free form. -/
theorem card_orderedPartitions_mul_prod_factorial :
    ∀ {k : ℕ} (A : Finset α) (c : Fin k → ℕ), ∑ i, c i = A.card →
      (A.orderedPartitions c).card * ∏ i, (c i)! = A.card ! := by
  intro k
  induction k with
  | zero =>
    intro A c hc
    have hA : A = ∅ := card_eq_zero.mp (by simpa using hc.symm)
    subst hA
    rw [orderedPartitions_of_isEmpty]
    simp
  | succ k IH =>
    intro A c hc
    have hsplit : c 0 + ∑ i : Fin k, c i.succ = A.card := by
      rw [← hc, Fin.sum_univ_succ]
    have hc0 : c 0 ≤ A.card := hsplit ▸ Nat.le_add_right _ _
    have hfib : (A.orderedPartitions c).card
        = ∑ S ∈ A.powersetCard (c 0), ((A \ S).orderedPartitions (Fin.tail c)).card := by
      rw [card_eq_sum_card_fiberwise (f := fun T => T 0) (t := A.powersetCard (c 0)) ?_]
      · refine sum_congr rfl fun S hS => ?_
        rw [mem_powersetCard] at hS
        exact card_filter_orderedPartitions A S c hS.1 hS.2
      · intro T hT
        rw [mem_coe, mem_orderedPartitions] at hT
        exact mem_coe.mpr (mem_powersetCard.mpr ⟨hT.1 0, hT.2.1 0⟩)
    have hterm : ∀ S ∈ A.powersetCard (c 0),
        ((A \ S).orderedPartitions (Fin.tail c)).card * ∏ i : Fin k, (c i.succ)!
          = (A.card - c 0)! := by
      intro S hS
      rw [mem_powersetCard] at hS
      have hcard : (A \ S).card = A.card - c 0 := by
        rw [card_sdiff_of_subset hS.1, hS.2]
      have h := IH (A \ S) (Fin.tail c)
        (by rw [hcard]; simpa [Fin.tail] using (by omega : ∑ i : Fin k, c i.succ = A.card - c 0))
      rw [hcard] at h
      simpa [Fin.tail] using h
    calc (A.orderedPartitions c).card * ∏ i, (c i)!
        = (∑ S ∈ A.powersetCard (c 0), ((A \ S).orderedPartitions (Fin.tail c)).card) *
            ((c 0)! * ∏ i : Fin k, (c i.succ)!) := by rw [hfib, Fin.prod_univ_succ]
      _ = (∑ S ∈ A.powersetCard (c 0),
            ((A \ S).orderedPartitions (Fin.tail c)).card * ∏ i : Fin k, (c i.succ)!) *
              (c 0)! := by
          rw [sum_mul, sum_mul]
          exact sum_congr rfl fun S _ => by
            rw [← mul_assoc, mul_right_comm]
      _ = (∑ _S ∈ A.powersetCard (c 0), (A.card - c 0)!) * (c 0)! := by
          rw [sum_congr rfl hterm]
      _ = A.card.choose (c 0) * (c 0)! * (A.card - c 0)! := by
          rw [sum_const, card_powersetCard, smul_eq_mul, mul_right_comm]
      _ = A.card ! := Nat.choose_mul_factorial_mul_factorial hc0

/-- **The multinomial coefficient counts ordered partitions of a finset with prescribed
block sizes.** -/
theorem card_orderedPartitions {k : ℕ} (A : Finset α) (c : Fin k → ℕ)
    (hc : ∑ i, c i = A.card) :
    (A.orderedPartitions c).card = A.card ! / ∏ i, (c i)! := by
  rw [← card_orderedPartitions_mul_prod_factorial A c hc, Nat.mul_div_cancel]
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

end Finset
