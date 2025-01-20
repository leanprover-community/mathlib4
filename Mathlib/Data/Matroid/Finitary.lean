/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Invariance of cardinality of bases of a finitary matroid

In a finitary matroid, any two bases have the same cardinality.
-/

namespace Matroid.Base

variable {α : Type*} {M : Matroid α} {B B' : Set α} (hB : M.Base B) (hB' : M.Base B') [M.Finitary]
include hB hB'

open Cardinal Set

private theorem cardinalMk_le_of_finitary : #B ≤ #B' := by
  by_cases h : B'.Finite
  · rw [← cast_ncard h, ← cast_ncard (hB'.finite_of_finite h hB), hB.ncard_eq_ncard_of_base hB']
  rw [← Set.Infinite, ← infinite_coe_iff] at h
  have (a : α) (ha : a ∈ B' \ B) : ∃ S : Set α, Finite S ∧ S ⊆ B ∧ ¬ M.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin ↦ (this (J \ {a}) fin.diff.to_subtype <|
      diff_singleton_subset_iff.mpr hJ).subset (subset_insert_diff_singleton ..)
  choose S S_fin hSB dep using this
  let U := (B ∩ B') ∪ ⋃ a : ↥(B' \ B), S a a.2
  suffices B ⊆ U from
    (mk_le_mk_of_subset this).trans <| (mk_union_le ..).trans <|
      (add_le_add (mk_le_mk_of_subset inter_subset_right) <| (mk_iUnion_le _).trans <| mul_le_mul'
        (mk_le_mk_of_subset diff_subset) <| ciSup_le' fun _ ↦ (lt_aleph0_of_finite _).le).trans <|
    by rw [mul_aleph0_eq (aleph0_le_mk _), add_eq_self (aleph0_le_mk _)]
  have hUB : U ⊆ B := union_subset inter_subset_left (iUnion_subset fun a ↦ hSB a a.2)
  by_contra hBU
  have ⟨a, ha, ind⟩ := hB.exists_insert_of_ssubset ⟨hUB, hBU⟩ hB'
  have : a ∈ B' \ B := ⟨ha.1, fun haB ↦ ha.2 (.inl ⟨haB, ha.1⟩)⟩
  refine dep a this (ind.subset <| insert_subset_insert <| .trans ?_ subset_union_right)
  exact subset_iUnion_of_subset ⟨a, this⟩ subset_rfl

theorem cardinalMk_eq_of_finitary : #B = #B' :=
  (cardinalMk_le_of_finitary hB hB').antisymm (cardinalMk_le_of_finitary hB' hB)

end Matroid.Base
