/-
Copyright (c) 2025 Peter Nelson and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Junyan Xu
-/
import Mathlib.Data.Matroid.Closure
import Mathlib.Data.Matroid.Map
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal-valued rank

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if `I` and `J` are both bases for a set `X`,
then `#(I \ J) = #(J \ I)` and (consequently) `#I = #J`.
This file introduces a typeclass `CardinalRank` that applies to any matroid
such that this property holds for all `I`, `J` and `X`.

A matroid satisfying this condition has a well-defined cardinality-valued rank function,
both for itself and all its minors.

# Main Declarations

* `Matroid.CardinalRank` : a typeclass capturing the idea that a matroid and all its minors
  have a well-defined cardinal-valued rank function.
* `Matroid.cardRank M` is the rank of a matroid `M`, as a `Cardinal`.
* `Matroid.cardRk M X` is the rank of a set `X` in a matroid `M`, as a `Cardinal`.
* `cardinalRank_of_finitary` is the instance showing that `Finitary` matroids are `CardinalRank`.
* `cardRk_inter_add_cardRk_union_le` states that cardinal rank is submodular.

# Notes

It is not the case that all matroids are `CardinalRank`,
since the equicardinality of bases in general matroids is independent of ZFC
(see the module docstring of `Mathlib.Data.Matroid.Basic`).
Lemmas like `Matroid.Base.cardinalMk_diff_comm` become true for all matroids
only if they are weakened by replacing `Cardinal.mk`
with the cruder `ℕ∞`-valued `Set.encard`; see, for example, `Matroid.Base.encard_diff_comm`.

# TODO

* Higgs' theorem that, if the generalized continuum hypothesis holds,
  all bases of any matroid are equicardinal.
-/

variable {α : Type*} {M : Matroid α} {I J B B' X Y : Set α}

universe u

open Cardinal Set

namespace Matroid

section Basic

/-- A class stating that cardinality-valued rank is well-defined for a matroid `M` and its minors.
This holds for `Finitary` matroids.  -/
@[mk_iff]
class CardinalRank (M : Matroid α) : Prop where
  forall_card_basis_diff :
    ∀ ⦃I J X⦄, M.Basis I X → M.Basis J X → #(I \ J : Set α) = #(J \ I : Set α)

variable [CardinalRank M]

theorem Basis.cardinalMk_diff_comm (hIX : M.Basis I X) (hJX : M.Basis J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  CardinalRank.forall_card_basis_diff hIX hJX

theorem Basis'.cardinalMk_diff_comm (hIX : M.Basis' I X) (hJX : M.Basis' J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  hIX.basis_inter_ground.cardinalMk_diff_comm hJX.basis_inter_ground

theorem Base.cardinalMk_diff_comm (hB : M.Base B) (hB' : M.Base B') :
    #(B \ B' : Set α) = #(B' \ B : Set α) :=
  hB.basis_ground.cardinalMk_diff_comm hB'.basis_ground

theorem Basis.cardinalMk_eq (hIX : M.Basis I X) (hJX : M.Basis J X) : #I = #J := by
  rw [← diff_union_inter I J,
    mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right),
    hIX.cardinalMk_diff_comm hJX,
    ← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left),
    inter_comm, diff_union_inter]

theorem Basis'.cardinalMk_eq (hIX : M.Basis' I X) (hJX : M.Basis' J X) : #I = #J :=
  hIX.basis_inter_ground.cardinalMk_eq hJX.basis_inter_ground

theorem Base.cardinalMk_eq (hB : M.Base B) (hB' : M.Base B') : #B = #B' :=
  hB.basis_ground.cardinalMk_eq hB'.basis_ground

theorem Indep.cardinalMk_le_base (hI : M.Indep I) (hB : M.Base B) : #I ≤ #B :=
  have ⟨_B', hB', hIB'⟩ := hI.exists_base_superset
  hB'.cardinalMk_eq hB ▸ mk_le_mk_of_subset hIB'

theorem Indep.cardinalMk_le_basis' (hI : M.Indep I) (hJ : M.Basis' J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  have ⟨_J', hJ', hIJ'⟩ := hI.subset_basis'_of_subset hIX
  hJ'.cardinalMk_eq hJ ▸ mk_le_mk_of_subset hIJ'

theorem Indep.cardinalMk_le_basis (hI : M.Indep I) (hJ : M.Basis J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  hI.cardinalMk_le_basis' hJ.basis' hIX

end Basic

section Instances

/-- `Finitary` matroids have a cardinality-valued rank function. -/
instance cardinalRank_of_finitary [Finitary M] : CardinalRank M := by
  suffices aux : ∀ ⦃B B'⦄ ⦃N : Matroid α⦄, Finitary N → N.Base B → N.Base B' →
      #(B \ B' : Set α) ≤ #(B' \ B : Set α) from
    ⟨fun I J X hI hJ ↦ (aux (restrict_finitary X) hI.base_restrict hJ.base_restrict).antisymm
      (aux (restrict_finitary X) hJ.base_restrict hI.base_restrict)⟩
  intro B B' N hfin hB hB'
  by_cases h : (B' \ B).Finite
  · rw [← cast_ncard h, ← cast_ncard, hB.ncard_diff_comm hB']
    exact (hB'.diff_finite_comm hB).mp h
  rw [← Set.Infinite, ← infinite_coe_iff] at h
  have (a : α) (ha : a ∈ B' \ B) : ∃ S : Set α, Finite S ∧ S ⊆ B ∧ ¬ N.Indep (insert a S) := by
    have := (hB.insert_dep ⟨hB'.subset_ground ha.1, ha.2⟩).1
    contrapose! this
    exact Finitary.indep_of_forall_finite _ fun J hJ fin ↦ (this (J \ {a}) fin.diff.to_subtype <|
      diff_singleton_subset_iff.mpr hJ).subset (subset_insert_diff_singleton ..)
  choose S S_fin hSB dep using this
  let U := ⋃ a : ↥(B' \ B), S a a.2
  suffices B \ B' ⊆ U by
    refine (mk_le_mk_of_subset this).trans <| (mk_iUnion_le ..).trans
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

/-- Restrictions of matroids with cardinal rank functions have cardinal rank functions- -/
instance cardinalRank_restrict [CardinalRank M] : CardinalRank (M ↾ X) := by
  refine ⟨fun I J Y hI hJ ↦ ?_⟩
  rw [basis_restrict_iff'] at hI hJ
  exact hI.1.cardinalMk_diff_comm hJ.1

instance cardinalRank_map {α β : Type u} {f : α → β} (M : Matroid α) [CardinalRank M]
    (hf : InjOn f M.E) : CardinalRank (M.map f hf) := by
  refine ⟨fun I J X hI hJ ↦ ?_⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := map_basis_iff'.1 hI
  obtain ⟨J, X', hJX, rfl, h'⟩ := map_basis_iff'.1 hJ
  obtain rfl : X = X' := by
    rwa [InjOn.image_eq_image_iff hf hIX.subset_ground hJX.subset_ground] at h'
  have hcard := hIX.cardinalMk_diff_comm hJX
  rwa [← mk_image_eq_of_injOn _ _ (hf.mono (diff_subset.trans hIX.indep.subset_ground)),
    ← mk_image_eq_of_injOn _ _ (hf.mono (diff_subset.trans hJX.indep.subset_ground)),
    (hf.mono hIX.indep.subset_ground).image_diff,
    (hf.mono hJX.indep.subset_ground).image_diff, inter_comm,
    hf.image_inter hJX.indep.subset_ground hIX.indep.subset_ground,
    diff_inter_self_eq_diff, diff_self_inter] at hcard

end Instances

section Rank

/-- The rank (size of a largest base) of a matroid `M` as a `Cardinal`. -/
noncomputable def cardRank (M : Matroid α) := ⨆ (B : {B // M.Base B}), #B

/-- The rank (size of a largest basis) of a set `X` in a matroid `M`, as a `Cardinal`. -/
noncomputable def cardRk (M : Matroid α) (X : Set α) := (M ↾ X).cardRank

theorem Base.cardinalMk_le_cardRank (hB : M.Base B) : #B ≤ M.cardRank :=
  le_ciSup (f := fun (B : {B // M.Base B}) ↦ #(B.1)) (bddAbove_range _) ⟨B, hB⟩

theorem Basis'.cardinalMk_le_cardRk (hIX : M.Basis' I X) : #I ≤ M.cardRk X :=
  (base_restrict_iff'.2 hIX).cardinalMk_le_cardRank

theorem Basis.cardinalMk_le_cardRk (hIX : M.Basis I X) : #I ≤ M.cardRk X :=
  hIX.basis'.cardinalMk_le_cardRk

theorem cardRank_le_iff {κ : Cardinal} : M.cardRank ≤ κ ↔ ∀ ⦃B⦄, M.Base B → #B ≤ κ :=
  ⟨fun h _ hB ↦ (hB.cardinalMk_le_cardRank.trans h), fun h ↦ ciSup_le fun ⟨_, hB⟩ ↦ h hB⟩

theorem cardRk_le_iff {κ : Cardinal} : M.cardRk X ≤ κ ↔ ∀ ⦃I⦄, M.Basis' I X → #I ≤ κ := by
  simp_rw [cardRk, cardRank_le_iff, base_restrict_iff']

theorem Indep.cardinalMk_le_cardRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : #I ≤ M.cardRk X :=
  let ⟨_, hJ, hIJ⟩ := hI.subset_basis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cardRk

theorem cardRk_le_cardinalMk (M : Matroid α) (X : Set α) : M.cardRk X ≤ #X :=
  ciSup_le fun ⟨_, hI⟩ ↦ mk_le_mk_of_subset hI.subset_ground

@[simp] theorem cardRk_ground (M : Matroid α) : M.cardRk M.E = M.cardRank := by
  rw [cardRk, restrict_ground_eq_self]

@[simp] theorem cardRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).cardRank = M.cardRk X := rfl

theorem cardRk_mono (M : Matroid α) : Monotone M.cardRk := by
  simp only [Monotone, le_eq_subset, cardRk_le_iff]
  intro X Y hXY I hIX
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_basis'_of_subset (hIX.subset.trans hXY)
  exact (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cardRk

theorem cardRk_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.cardRk X ≤ M.cardRk Y :=
  M.cardRk_mono hXY

@[simp] theorem cardRk_inter_ground (M : Matroid α) (X : Set α) :
    M.cardRk (X ∩ M.E) = M.cardRk X :=
  (M.cardRk_le_of_subset inter_subset_left).antisymm <|
    cardRk_le_iff.2 fun _ h ↦ h.basis_inter_ground.cardinalMk_le_cardRk

theorem cardRk_restrict_subset (M : Matroid α) (hYX : Y ⊆ X) : (M ↾ X).cardRk Y = M.cardRk Y := by
  have aux : ∀ ⦃I⦄, M.Basis' I Y ↔ (M ↾ X).Basis' I Y := by
    simp_rw [basis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h ↦ h.subset.trans hYX
  simp_rw [le_antisymm_iff, cardRk_le_iff]
  exact ⟨fun I hI ↦ (aux.2 hI).cardinalMk_le_cardRk, fun I hI ↦ (aux.1 hI).cardinalMk_le_cardRk⟩

theorem cardRk_restrict (M : Matroid α) (X Y : Set α) : (M ↾ X).cardRk Y = M.cardRk (X ∩ Y) := by
  rw [← cardRk_inter_ground, restrict_ground_eq, cardRk_restrict_subset _ inter_subset_right,
    inter_comm]

theorem Indep.cardRk_eq_cardinalMk (hI : M.Indep I) : #I = M.cardRk I :=
  (M.cardRk_le_cardinalMk I).antisymm' (hI.basis_self.cardinalMk_le_cardRk)

@[simp] theorem cardRk_map_eq {α β : Type u} {f : α → β} {X : Set α} (M : Matroid α)
    [CardinalRank M] (hf : InjOn f M.E) (hX : X ⊆ M.E := by aesop_mat) :
    (M.map f hf).cardRk (f '' X) = M.cardRk X := by
  simp_rw [le_antisymm_iff, cardRk_le_iff, basis'_iff_basis hX,
    basis'_iff_basis (show f '' X ⊆ (M.map f hf).E from image_mono hX)]
  refine ⟨fun I hI ↦ ?_, fun I hI ↦ le_of_eq_of_le ?_ (hI.map hf).cardinalMk_le_cardRk ⟩
  · obtain ⟨I, X', hIX, rfl, hXX'⟩ := map_basis_iff'.1 hI
    obtain rfl : X = X' := by rwa [hf.image_eq_image_iff hX hIX.subset_ground] at hXX'
    rw [mk_image_eq_of_injOn _ _ (hf.mono hIX.indep.subset_ground)]
    exact hIX.cardinalMk_le_cardRk
  rw [mk_image_eq_of_injOn _ _ (hf.mono hI.indep.subset_ground)]

variable [CardinalRank M]

theorem Base.cardinalMk_eq_cardRank (hB : M.Base B) : #B = M.cardRank := by
  have : Nonempty {B : Set α // M.Base B} := ⟨M.exists_base.choose, M.exists_base.choose_spec⟩
  have hrw : ∀ B' : {B : Set α // M.Base B}, #B' = #B := fun B' ↦ B'.2.cardinalMk_eq hB
  simp [cardRank, hrw]

theorem Basis'.cardinalMk_eq_cardRk (hIX : M.Basis' I X) : #I = M.cardRk X := by
  rw [cardRk, (base_restrict_iff'.2 hIX).cardinalMk_eq_cardRank]

theorem Basis.cardinalMk_eq_cardRk (hIX : M.Basis I X) : #I = M.cardRk X :=
  hIX.basis'.cardinalMk_eq_cardRk

@[simp] theorem cardRk_closure (M : Matroid α) [CardinalRank M] (X : Set α) :
    M.cardRk (M.closure X) = M.cardRk X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.basis_closure_right.cardinalMk_eq_cardRk, ← hI.cardinalMk_eq_cardRk]

theorem cardRk_closure_congr (hXY : M.closure X = M.closure Y) : M.cardRk X = M.cardRk Y := by
  rw [← cardRk_closure, hXY, cardRk_closure]

@[simp] theorem cardRk_union_closure_right_eq (M : Matroid α) [CardinalRank M] (X Y : Set α) :
    M.cardRk (X ∪ M.closure Y) = M.cardRk (X ∪ Y) :=
  M.cardRk_closure_congr (M.closure_union_closure_right_eq _ _)

@[simp] theorem cardRk_union_closure_left_eq (M : Matroid α) [CardinalRank M] (X Y : Set α) :
    M.cardRk (M.closure X ∪ Y) = M.cardRk (X ∪ Y) :=
  M.cardRk_closure_congr (M.closure_union_closure_left_eq _ _)

@[simp] theorem cardRk_insert_closure_eq (M : Matroid α) [CardinalRank M] (e : α) (X : Set α) :
    M.cardRk (insert e (M.closure X)) = M.cardRk (insert e X) := by
  rw [← union_singleton, cardRk_union_closure_left_eq, union_singleton]

theorem cardRk_union_closure_eq (M : Matroid α) [CardinalRank M] (X Y : Set α) :
    M.cardRk (M.closure X ∪ M.closure Y) = M.cardRk (X ∪ Y) := by
  simp

/-- The `Cardinal` rank function is submodular. -/
theorem cardRk_inter_add_cardRk_union_le (M : Matroid α) [CardinalRank M] (X Y : Set α) :
    M.cardRk (X ∩ Y) + M.cardRk (X ∪ Y) ≤ M.cardRk X + M.cardRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_basis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_basis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← cardRk_union_closure_eq, ← hIX.closure_eq_closure, ← hIY.closure_eq_closure,
    cardRk_union_closure_eq, ← hIi.cardinalMk_eq_cardRk, ← hIX.cardinalMk_eq_cardRk,
    ← hIY.cardinalMk_eq_cardRk, ← mk_union_add_mk_inter, add_comm]
  exact add_le_add (M.cardRk_le_cardinalMk _) (mk_le_mk_of_subset (subset_inter hIX' hIY'))

end Rank

end Matroid
