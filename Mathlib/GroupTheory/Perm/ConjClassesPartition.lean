/-
Copyright (c) 2026 Keith Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes

/-!
# Conjugacy classes of `Perm α` and partitions of `Fintype.card α`

`Equiv.Perm.partition` sends a permutation to its cycle type padded with fixed points, a partition
of `Fintype.card α`, and `Equiv.Perm.partition_eq_of_isConj` says two permutations are conjugate iff
their partitions agree.  Together with `Equiv.Perm.exists_with_cycleType_iff` (every admissible
cycle type is realised) this gives the classical bijection

`Equiv.Perm.conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition`.
-/

@[expose] public section

namespace Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The partition of a conjugacy class of permutations. -/
def conjClassesPartition : ConjClasses (Perm α) → (Fintype.card α).Partition :=
  Quotient.lift partition fun _ _ (h : IsConj _ _) => partition_eq_of_isConj.1 h

@[simp]
theorem conjClassesPartition_mk (σ : Perm α) :
    conjClassesPartition (ConjClasses.mk σ) = σ.partition := rfl

theorem conjClassesPartition_injective :
    Function.Injective (conjClassesPartition : ConjClasses (Perm α) → _) := by
  intro c c' h
  obtain ⟨σ, rfl⟩ := ConjClasses.exists_rep c
  obtain ⟨τ, rfl⟩ := ConjClasses.exists_rep c'
  rw [conjClassesPartition_mk, conjClassesPartition_mk] at h
  exact ConjClasses.mk_eq_mk_iff_isConj.2 (partition_eq_of_isConj.2 h)

/-- Every partition of `Fintype.card α` is the partition of some permutation. -/
theorem exists_partition_eq (p : (Fintype.card α).Partition) : ∃ σ : Perm α, σ.partition = p := by
  classical
  set m := p.parts.filter fun a => 2 ≤ a with hm
  set r := p.parts.filter fun a => ¬ 2 ≤ a with hr
  have hsplit : p.parts = m + r := (Multiset.filter_add_not _ _).symm
  have hr1 : r = Multiset.replicate (Multiset.card r) 1 := by
    rw [Multiset.eq_replicate]
    refine ⟨rfl, fun b hb => ?_⟩
    rw [hr, Multiset.mem_filter] at hb
    have := p.parts_pos hb.1
    omega
  have hsum : m.sum + Multiset.card r = Fintype.card α := by
    have := p.parts_sum
    rw [hsplit, Multiset.sum_add, hr1, Multiset.sum_replicate, smul_eq_mul, mul_one] at this
    exact this
  obtain ⟨σ, hσ⟩ := (exists_with_cycleType_iff (α := α) (m := m)).2
    ⟨by omega, fun a ha => (Multiset.mem_filter.1 ha).2⟩
  refine ⟨σ, Nat.Partition.ext ?_⟩
  rw [parts_partition, hσ, ← sum_cycleType, hσ, hsplit, hr1]
  congr 2
  omega

theorem conjClassesPartition_surjective :
    Function.Surjective (conjClassesPartition : ConjClasses (Perm α) → _) := fun p => by
  obtain ⟨σ, hσ⟩ := exists_partition_eq p
  exact ⟨ConjClasses.mk σ, by rw [conjClassesPartition_mk, hσ]⟩

/-- Conjugacy classes of `Perm α` correspond to partitions of `Fintype.card α`. -/
noncomputable def conjClassesEquivPartition : ConjClasses (Perm α) ≃ (Fintype.card α).Partition :=
  Equiv.ofBijective _ ⟨conjClassesPartition_injective, conjClassesPartition_surjective⟩

omit [DecidableEq α] in
theorem card_conjClasses_eq_card_partition :
    Nat.card (ConjClasses (Perm α)) = Nat.card ((Fintype.card α).Partition) := by
  classical
  exact Nat.card_congr conjClassesEquivPartition

end Equiv.Perm
