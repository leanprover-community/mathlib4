/-
Copyright (c) 2026 Kevin Gomez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Gomez
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Young diagram of a partition

This file defines the equivalence between Young diagrams `μ` with cardinality `n` and
partitions of `n`, where each row of the diagram becomes a part of the partition.
The two directions are `YoungDiagram.toPartition` and `YoungDiagram.ofPartition`.

Using this equivalence, the conjugate of a partition is also defined. Given the Young
diagram `μ` representing a partition `λ`, its conjugate `λ'` is the partition obtained
by flipping `μ` about the main diagonal, i.e. the columns of `μ` are the parts of `λ'`.
This is implemented here directly via `YoungDiagram.transpose`.

-/

@[expose] public section

namespace YoungDiagram

/-- Convert a Young diagram to a partition. -/
def toPartition {n : ℕ} (μ : YoungDiagram) (h : μ.card = n) : Nat.Partition n where
  parts := μ.rowLens
  parts_pos := μ.pos_of_mem_rowLens _
  parts_sum := by simp [sum_rowLens_eq_card, h]

/-- Convert a partition to a Young diagram. -/
def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  ofRowLens
    (p.parts.sort (· ≥ ·))
    (Multiset.pairwise_sort p.parts (· ≥ ·)).sortedGE

@[simp]
theorem rowLens_ofPartition_eq_sort_parts {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
  grind [ofPartition, rowLens_ofRowLens_eq_self, Multiset.mem_sort]

@[simp]
theorem card_ofPartition {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).card = n := by
  rw [← sum_rowLens_eq_card, rowLens_ofPartition_eq_sort_parts]
  calc
    (p.parts.sort (· ≥ ·)).sum
      = (↑(p.parts.sort (· ≥ ·)) : Multiset ℕ).sum := Multiset.sum_coe _
    _ = p.parts.sum := by rw [Multiset.sort_eq]
    _ = n := p.parts_sum

@[simp]
theorem ofPartition_toPartition {n : ℕ} {μ : YoungDiagram} (h : μ.card = n) :
    ofPartition (μ.toPartition h) = μ := by
  simp [ofPartition, toPartition, List.mergeSort_eq_self (· ≥ ·) μ.rowLens_sorted.pairwise,
    ofRowLens_to_rowLens_eq_self]

@[simp]
theorem toPartition_ofPartition {n : ℕ} {p : Nat.Partition n} :
    (ofPartition p).toPartition (card_ofPartition p) = p := by
  ext
  simp [toPartition]

/-- Equivalence between Young diagrams of cardinality `n` and partitions of `n`. -/
def equivPartition {n : ℕ} : { μ : YoungDiagram // μ.card = n } ≃ Nat.Partition n where
  toFun μ := toPartition μ μ.2
  invFun p := ⟨ofPartition p, card_ofPartition p⟩
  left_inv := fun ⟨_, h⟩ => Subtype.mk_eq_mk.mpr (ofPartition_toPartition h)
  right_inv := fun _ => toPartition_ofPartition

end YoungDiagram

namespace Nat.Partition

/-- Conjugate a partition (equivalent to transposing its Young diagram). -/
def conjugate {n : ℕ} (p : Partition n) : Partition n :=
  (YoungDiagram.ofPartition p).transpose.toPartition (by
    rw [YoungDiagram.card_transpose, YoungDiagram.card_ofPartition]
  )

/-- Conjugation is an involution. -/
@[simp]
theorem conjugate_conjugate {n : ℕ} (p : Partition n) : p.conjugate.conjugate = p := by
  ext
  simp [conjugate]

end Nat.Partition
