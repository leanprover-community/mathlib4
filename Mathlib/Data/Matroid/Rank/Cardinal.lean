/-
Copyright (c) 2025 Peter Nelson and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Junyan Xu
-/
import Mathlib.Data.Matroid.Restrict
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Invariance of cardinality of bases of a finitary matroid

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if `B` and `B'` are bases, then `#(B \ B') = #(B' \ B)`.
This file provides proofs of these facts,
as well as variants when each of `B` and `B'` is a `Basis` or `Basis'` of some common set `X`.

Some extra assumption like `Finitary` is necessary for these to be true,
since the equicardinality of bases in general matroids is independent of ZFC
(see the docstring of `Data.Matroid.Basic`).
Lemmas like `Matroid.Base.cardinalMk_diff_comm_of_finitary`
become true for all matroids if they are weakened by replacing `Cardinal.mk`
with the cruder `ℕ∞`-valued `encard`; see, for example, `Matroid.Base.encard_diff_comm`.

TODO

* Higg's theorem that, if the generalized continuum hypothesis holds,
  all bases of any matroid are equicardinal.
* API for a `Cardinal`-valued rank function.
-/

variable {α : Type*} {M : Matroid α} {I J B B' X : Set α} [M.Finitary]

open Cardinal Set

namespace Matroid

theorem Base.cardinalMk_diff_comm_of_finitary (hB : M.Base B) (hB' : M.Base B') :
    #(B \ B' : Set α) = #(B' \ B : Set α) := by
  wlog hge : #(B' \ B : Set α) ≤ #(B \ B' : Set α) with aux
  · exact (aux hB' hB (not_le.1 hge).le).symm
  by_cases h : (B' \ B).Finite
  · rw [← cast_ncard h, ← cast_ncard, hB.ncard_diff_comm hB']
    exact (diff_finite_comm hB' hB).mp h
  rw [← Set.Infinite, ← infinite_coe_iff] at h
  have (a : α) (ha : a ∈ B' \ B) : ∃ S : Set α, Finite S ∧ S ⊆ B ∧ ¬ M.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin ↦ (this (J \ {a}) fin.diff.to_subtype <|
      diff_singleton_subset_iff.mpr hJ).subset (subset_insert_diff_singleton ..)
  choose S S_fin hSB dep using this
  let U := ⋃ a : ↥(B' \ B), S a a.2
  suffices B \ B' ⊆ U by
    refine hge.antisymm' <| (mk_le_mk_of_subset this).trans <| (mk_iUnion_le ..).trans
      <| (mul_le_max_of_aleph0_le_left (by simp)).trans ?_
    simp only [sup_le_iff, le_refl, true_and]
    exact ciSup_le' fun e ↦ (lt_aleph0_of_finite _).le.trans <| by simp
  rw [← diff_inter_self_eq_diff, diff_subset_iff, inter_comm]
  have hUB : (B ∩ B') ∪ U ⊆ B :=
    union_subset inter_subset_left (iUnion_subset fun e ↦ (hSB e.1 e.2))
  by_contra hBU
  have ⟨a, ha, ind⟩ := hB.exists_insert_of_ssubset ⟨hUB, hBU⟩ hB'
  have : a ∈ B' \ B := ⟨ha.1, fun haB ↦ ha.2 (.inl ⟨haB, ha.1⟩)⟩
  refine dep a this (ind.subset <| insert_subset_insert <| .trans ?_ subset_union_right)
  exact subset_iUnion_of_subset ⟨a, this⟩ subset_rfl

theorem Base.cardinalMk_eq_of_finitary (hB : M.Base B) (hB' : M.Base B') : #B = #B' := by
  rw [← diff_union_inter B B',
    mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right),
    hB.cardinalMk_diff_comm_of_finitary hB',
    ← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left),
    inter_comm, diff_union_inter]

theorem Basis'.cardinalMk_diff_comm_of_finitary (hIX : M.Basis' I X) (hJX : M.Basis' J X) :
    #(I \ J : Set α) = #(J \ I : Set α) := by
  rw [← base_restrict_iff'] at hIX hJX
  rw [hIX.cardinalMk_diff_comm_of_finitary hJX]

theorem Basis.cardinalMk_diff_comm_of_finitary (hIX : M.Basis I X) (hJX : M.Basis J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  hIX.basis'.cardinalMk_diff_comm_of_finitary hJX.basis'

theorem Basis'.cardinalMk_eq_of_finitary (hIX : M.Basis' I X) (hJX : M.Basis' J X) : #I = #J := by
  rw [← base_restrict_iff'] at hIX hJX
  rw [hIX.cardinalMk_eq_of_finitary hJX]

theorem Basis.cardinalMk_eq_of_finitary (hIX : M.Basis I X) (hJX : M.Basis J X) : #I = #J :=
  hIX.basis'.cardinalMk_eq_of_finitary hJX.basis'

theorem Indep.cardinalMk_le_base_of_finitary (hI : M.Indep I) (hB : M.Base B) : #I ≤ #B :=
  have ⟨_B', hB', hIB'⟩ := hI.exists_base_superset
  hB'.cardinalMk_eq_of_finitary hB ▸ mk_le_mk_of_subset hIB'

theorem Indep.cardinalMk_le_basis'_of_finitary (hI : M.Indep I) (hJ : M.Basis' J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  have ⟨_J', hJ', hIJ'⟩ := hI.subset_basis'_of_subset hIX
  hJ'.cardinalMk_eq_of_finitary hJ ▸ mk_le_mk_of_subset hIJ'

theorem Indep.cardinalMk_le_basis_of_finitary (hI : M.Indep I) (hJ : M.Basis J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  hI.cardinalMk_le_basis'_of_finitary hJ.basis' hIX

end Matroid
