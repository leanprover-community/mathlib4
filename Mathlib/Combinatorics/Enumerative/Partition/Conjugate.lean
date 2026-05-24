/-
Copyright (c) 2026 Kevin Gomez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Gomez
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Conjugate of a partition

Given the Young diagram `μ` representing a partition `λ`, its conjugate `λ'` is the partition
obtained by flipping `μ` about the main diagonal, i.e. the columns of `μ` are the parts of `λ'`.
This is implemented here directly via `YoungDiagram.transpose`.

See `YoungDiagram.ofPartition` and `YoungDiagram.toPartition` for direct manipulation of diagrams
arising from partitions.
-/

@[expose] public section

namespace Nat.Partition

/-- Conjugate a partition (equivalent to transposing its Young diagram). -/
def conjugate {n : ℕ} (p : Partition n) : Partition n :=
  (YoungDiagram.ofPartition p).transpose.toPartition (by
    rw [YoungDiagram.transpose_card_eq_card, YoungDiagram.card_ofPartition]
  )

/-- Conjugation is an involution. -/
@[simp]
theorem conjugate_conjugate {n : ℕ} (p : Partition n) : p.conjugate.conjugate = p := by
  ext
  simp [conjugate]

end Nat.Partition
