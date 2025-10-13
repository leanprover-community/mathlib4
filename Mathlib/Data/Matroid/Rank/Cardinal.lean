/-
Copyright (c) 2025 Peter Nelson and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Junyan Xu
-/
import Mathlib.Data.Matroid.Map
import Mathlib.Data.Matroid.Rank.ENat
import Mathlib.Data.Matroid.Rank.Finite
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal-valued rank

In a finitary matroid, all bases have the same cardinality.
In fact, something stronger holds: if each of `I` and `J` is a basis for a set `X`,
then `#(I \ J) = #(J \ I)` and (consequently) `#I = #J`.
This file introduces a typeclass `InvariantCardinalRank` that applies to any matroid
such that this property holds for all `I`, `J` and `X`.

A matroid satisfying this condition has a well-defined cardinality-valued rank function,
both for itself and all its minors.

# Main Declarations

* `Matroid.InvariantCardinalRank` : a typeclass capturing the idea that a matroid and all its minors
  have a well-behaved cardinal-valued rank function.
* `Matroid.cRank M` is the supremum of the cardinalities of the bases of matroid `M`.
* `Matroid.cRk M X` is the supremum of the cardinalities of the bases of a set `X` in a matroid `M`.
* `invariantCardinalRank_of_finitary` is the instance
  showing that `Finitary` matroids are `InvariantCardinalRank`.
* `cRk_inter_add_cRk_union_le` states that cardinal rank is submodular.

# Notes

It is not (provably) the case that all matroids are `InvariantCardinalRank`,
since the equicardinality of bases in general matroids is independent of ZFC
(see the module docstring of `Mathlib/Data/Matroid/Basic.lean`).
Lemmas like `Matroid.Base.cardinalMk_diff_comm` become true for all matroids
only if they are weakened by replacing `Cardinal.mk` with the cruder `ℕ∞`-valued `Set.encard`.
The `ℕ∞`-valued rank and rank functions `Matroid.eRank` and `Matroid.eRk`,
which have a more unconditionally strong API,
are developed in `Mathlib/Data/Matroid/Rank/ENat.lean`.

# Implementation Details

Since the functions `cRank` and `cRk` are defined as suprema,
independently of the `Matroid.InvariantCardinalRank` typeclass,
they are well-defined for all matroids.
However, for matroids that do not satisfy `InvariantCardinalRank`, they are badly behaved.
For instance, in general `cRk` is not submodular,
and its value may differ on a set `X` and the closure of `X`.
We state and prove theorems without `InvariantCardinalRank` whenever possible,
which sometime makes their proofs longer than they would be with the instance.

# TODO

* Higgs' theorem : if the generalized continuum hypothesis holds,
  then every matroid is `InvariantCardinalRank`.

-/

universe u v

variable {α : Type u} {β : Type v} {f : α → β} {M : Matroid α} {I J B B' X Y : Set α}

open Cardinal Set

namespace Matroid

section Rank

variable {κ : Cardinal}

/-- The rank (supremum of the cardinalities of bases) of a matroid `M` as a `Cardinal`.
See `Matroid.eRank` for a better-behaved `ℕ∞`-valued version. -/
noncomputable def cRank (M : Matroid α) := ⨆ B : {B // M.IsBase B}, #B

/-- The rank (supremum of the cardinalities of bases) of a set `X` in a matroid `M`,
as a `Cardinal`. See `Matroid.eRk` for a better-behaved `ℕ∞`-valued version. -/
noncomputable def cRk (M : Matroid α) (X : Set α) := (M ↾ X).cRank

theorem IsBase.cardinalMk_le_cRank (hB : M.IsBase B) : #B ≤ M.cRank :=
  le_ciSup (f := fun B : {B // M.IsBase B} ↦ #B.1) (bddAbove_range _) ⟨B, hB⟩

theorem Indep.cardinalMk_le_cRank (ind : M.Indep I) : #I ≤ M.cRank :=
  have ⟨B, isBase, hIB⟩ := ind.exists_isBase_superset
  le_ciSup_of_le (bddAbove_range _) ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

theorem cRank_eq_iSup_cardinalMk_indep : M.cRank = ⨆ I : {I // M.Indep I}, #I :=
  (ciSup_le' fun B ↦ le_ciSup_of_le (bddAbove_range _) ⟨B, B.2.indep⟩ <| by rfl).antisymm <|
    ciSup_le' fun I ↦
      have ⟨B, isBase, hIB⟩ := I.2.exists_isBase_superset
      le_ciSup_of_le (bddAbove_range _) ⟨B, isBase⟩ (mk_le_mk_of_subset hIB)

theorem IsBasis'.cardinalMk_le_cRk (hIX : M.IsBasis' I X) : #I ≤ M.cRk X :=
  (isBase_restrict_iff'.2 hIX).cardinalMk_le_cRank

theorem IsBasis.cardinalMk_le_cRk (hIX : M.IsBasis I X) : #I ≤ M.cRk X :=
  hIX.isBasis'.cardinalMk_le_cRk

theorem cRank_le_iff : M.cRank ≤ κ ↔ ∀ ⦃B⦄, M.IsBase B → #B ≤ κ :=
  ⟨fun h _ hB ↦ (hB.cardinalMk_le_cRank.trans h), fun h ↦ ciSup_le fun ⟨_, hB⟩ ↦ h hB⟩

theorem cRk_le_iff : M.cRk X ≤ κ ↔ ∀ ⦃I⦄, M.IsBasis' I X → #I ≤ κ := by
  simp_rw [cRk, cRank_le_iff, isBase_restrict_iff']

theorem Indep.cardinalMk_le_cRk_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : #I ≤ M.cRk X :=
  let ⟨_, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

theorem cRk_le_cardinalMk (M : Matroid α) (X : Set α) : M.cRk X ≤ #X :=
  ciSup_le fun ⟨_, hI⟩ ↦ mk_le_mk_of_subset hI.subset_ground

@[simp] theorem cRk_ground (M : Matroid α) : M.cRk M.E = M.cRank := by
  rw [cRk, restrict_ground_eq_self]

@[simp] theorem cRank_restrict (M : Matroid α) (X : Set α) : (M ↾ X).cRank = M.cRk X := rfl

theorem cRk_mono (M : Matroid α) : Monotone M.cRk := by
  simp only [Monotone, le_eq_subset, cRk_le_iff]
  intro X Y hXY I hIX
  obtain ⟨J, hJ, hIJ⟩ := hIX.indep.subset_isBasis'_of_subset (hIX.subset.trans hXY)
  exact (mk_le_mk_of_subset hIJ).trans hJ.cardinalMk_le_cRk

theorem cRk_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.cRk X ≤ M.cRk Y :=
  M.cRk_mono hXY

@[simp] theorem cRk_inter_ground (M : Matroid α) (X : Set α) : M.cRk (X ∩ M.E) = M.cRk X :=
  (M.cRk_le_of_subset inter_subset_left).antisymm <| cRk_le_iff.2
    fun _ h ↦ h.isBasis_inter_ground.cardinalMk_le_cRk

theorem cRk_restrict_subset (M : Matroid α) (hYX : Y ⊆ X) : (M ↾ X).cRk Y = M.cRk Y := by
  have aux : ∀ ⦃I⦄, M.IsBasis' I Y ↔ (M ↾ X).IsBasis' I Y := by
    simp_rw [isBasis'_restrict_iff, inter_eq_self_of_subset_left hYX, iff_self_and]
    exact fun I h ↦ h.subset.trans hYX
  simp_rw [le_antisymm_iff, cRk_le_iff]
  exact ⟨fun I hI ↦ (aux.2 hI).cardinalMk_le_cRk, fun I hI ↦ (aux.1 hI).cardinalMk_le_cRk⟩

theorem cRk_restrict (M : Matroid α) (X Y : Set α) : (M ↾ X).cRk Y = M.cRk (X ∩ Y) := by
  rw [← cRk_inter_ground, restrict_ground_eq, cRk_restrict_subset _ inter_subset_right,
    inter_comm]

theorem Indep.cRk_eq_cardinalMk (hI : M.Indep I) : #I = M.cRk I :=
  (M.cRk_le_cardinalMk I).antisymm' (hI.isBasis_self.cardinalMk_le_cRk)

@[simp] theorem cRk_map_image_lift (M : Matroid α) (hf : InjOn f M.E) (X : Set α)
    (hX : X ⊆ M.E := by aesop_mat) : lift.{u,v} ((M.map f hf).cRk (f '' X)) = lift (M.cRk X) := by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup (bddAbove_range _), cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup (bddAbove_range _)]
  simp only [ciSup_le_iff (bddAbove_range _), ge_iff_le, Subtype.forall, isBase_restrict_iff',
    isBasis'_iff_isBasis hX, isBasis'_iff_isBasis (show f '' X ⊆ (M.map f hf).E from image_mono hX)]
  refine ⟨fun I hI ↦ ?_, fun I hI ↦ ?_⟩
  · obtain ⟨I, X', hIX, rfl, hXX'⟩ := map_isBasis_iff'.1 hI
    rw [mk_image_eq_of_injOn_lift _ _ (hf.mono hIX.indep.subset_ground), lift_le]
    obtain rfl : X = X' := by rwa [hf.image_eq_image_iff hX hIX.subset_ground] at hXX'
    exact hIX.cardinalMk_le_cRk
  rw [← mk_image_eq_of_injOn_lift _ _ (hf.mono hI.indep.subset_ground), lift_le]
  exact (hI.map hf).cardinalMk_le_cRk

@[simp] theorem cRk_map_image {β : Type u} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).cRk (f '' X) = M.cRk X :=
  lift_inj.1 <| M.cRk_map_image_lift ..

theorem cRk_map_eq {β : Type u} {f : α → β} {X : Set β} (M : Matroid α) (hf : InjOn f M.E) :
    (M.map f hf).cRk X = M.cRk (f ⁻¹' X) := by
  rw [← M.cRk_inter_ground, ← M.cRk_map_image hf _, image_preimage_inter, ← map_ground _ _ hf,
    cRk_inter_ground]

@[simp] theorem cRk_comap_lift (M : Matroid β) (f : α → β) (X : Set α) :
    lift.{v,u} ((M.comap f).cRk X) = lift (M.cRk (f '' X)) := by
  nth_rw 1 [cRk, cRank, le_antisymm_iff, lift_iSup (bddAbove_range _), cRk, cRank, cRk, cRank]
  nth_rw 2 [lift_iSup (bddAbove_range _)]
  simp only [ciSup_le_iff (bddAbove_range _), ge_iff_le, Subtype.forall, isBase_restrict_iff',
    comap_isBasis'_iff, and_imp]
  refine ⟨fun I hI hfI hIX ↦ ?_, fun I hIX ↦ ?_⟩
  · rw [← mk_image_eq_of_injOn_lift _ _ hfI, lift_le]
    exact hI.cardinalMk_le_cRk
  obtain ⟨I₀, hI₀X, rfl, hfI₀⟩ := show ∃ I₀ ⊆ X, f '' I₀ = I ∧ InjOn f I₀ by
    obtain ⟨I₀, hI₀ss, hbij⟩ := exists_subset_bijOn (f ⁻¹' I ∩ X) f
    refine ⟨I₀, hI₀ss.trans inter_subset_right, ?_, hbij.injOn⟩
    rw [hbij.image_eq, image_preimage_inter, inter_eq_self_of_subset_left hIX.subset]
  rw [mk_image_eq_of_injOn_lift _ _ hfI₀, lift_le]
  exact IsBasis'.cardinalMk_le_cRk <| comap_isBasis'_iff.2 ⟨hIX, hfI₀, hI₀X⟩

@[simp] theorem cRk_comap {β : Type u} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).cRk X = M.cRk (f '' X) :=
  lift_inj.1 <| M.cRk_comap_lift ..

end Rank

section Invariant

/-- A class stating that cardinality-valued rank is well-defined
(i.e. all bases are equicardinal) for a matroid `M` and its minors.
Notably, this holds for `Finitary` matroids; see `Matroid.invariantCardinalRank_of_finitary`. -/
@[mk_iff]
class InvariantCardinalRank (M : Matroid α) : Prop where
  forall_card_isBasis_diff :
    ∀ ⦃I J X⦄, M.IsBasis I X → M.IsBasis J X → #(I \ J : Set α) = #(J \ I : Set α)

variable [InvariantCardinalRank M]

theorem IsBasis.cardinalMk_diff_comm (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  InvariantCardinalRank.forall_card_isBasis_diff hIX hJX

theorem IsBasis'.cardinalMk_diff_comm (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X) :
    #(I \ J : Set α) = #(J \ I : Set α) :=
  hIX.isBasis_inter_ground.cardinalMk_diff_comm hJX.isBasis_inter_ground

theorem IsBase.cardinalMk_diff_comm (hB : M.IsBase B) (hB' : M.IsBase B') :
    #(B \ B' : Set α) = #(B' \ B : Set α) :=
  hB.isBasis_ground.cardinalMk_diff_comm hB'.isBasis_ground

theorem IsBasis.cardinalMk_eq (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) : #I = #J := by
  rw [← diff_union_inter I J,
    mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_right),
    hIX.cardinalMk_diff_comm hJX,
    ← mk_union_of_disjoint (disjoint_sdiff_left.mono_right inter_subset_left),
    inter_comm, diff_union_inter]

theorem IsBasis'.cardinalMk_eq (hIX : M.IsBasis' I X) (hJX : M.IsBasis' J X) : #I = #J :=
  hIX.isBasis_inter_ground.cardinalMk_eq hJX.isBasis_inter_ground

theorem IsBase.cardinalMk_eq (hB : M.IsBase B) (hB' : M.IsBase B') : #B = #B' :=
  hB.isBasis_ground.cardinalMk_eq hB'.isBasis_ground

theorem Indep.cardinalMk_le_isBase (hI : M.Indep I) (hB : M.IsBase B) : #I ≤ #B :=
  have ⟨_B', hB', hIB'⟩ := hI.exists_isBase_superset
  hB'.cardinalMk_eq hB ▸ mk_le_mk_of_subset hIB'

theorem Indep.cardinalMk_le_isBasis' (hI : M.Indep I) (hJ : M.IsBasis' J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  have ⟨_J', hJ', hIJ'⟩ := hI.subset_isBasis'_of_subset hIX
  hJ'.cardinalMk_eq hJ ▸ mk_le_mk_of_subset hIJ'

theorem Indep.cardinalMk_le_isBasis (hI : M.Indep I) (hJ : M.IsBasis J X) (hIX : I ⊆ X) :
    #I ≤ #J :=
  hI.cardinalMk_le_isBasis' hJ.isBasis' hIX

theorem IsBase.cardinalMk_eq_cRank (hB : M.IsBase B) : #B = M.cRank := by
  have hrw : ∀ B' : {B : Set α // M.IsBase B}, #B' = #B := fun B' ↦ B'.2.cardinalMk_eq hB
  simp [cRank, hrw]

/-- Restrictions of matroids with cardinal rank functions have cardinal rank functions. -/
instance invariantCardinalRank_restrict [InvariantCardinalRank M] :
    InvariantCardinalRank (M ↾ X) := by
  refine ⟨fun I J Y hI hJ ↦ ?_⟩
  rw [isBasis_restrict_iff'] at hI hJ
  exact hI.1.cardinalMk_diff_comm hJ.1

theorem IsBasis'.cardinalMk_eq_cRk (hIX : M.IsBasis' I X) : #I = M.cRk X := by
  rw [cRk, (isBase_restrict_iff'.2 hIX).cardinalMk_eq_cRank]

theorem IsBasis.cardinalMk_eq_cRk (hIX : M.IsBasis I X) : #I = M.cRk X :=
  hIX.isBasis'.cardinalMk_eq_cRk

@[simp] theorem cRk_closure (M : Matroid α) [InvariantCardinalRank M] (X : Set α) :
    M.cRk (M.closure X) = M.cRk X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [← hI.isBasis_closure_right.cardinalMk_eq_cRk, ← hI.cardinalMk_eq_cRk]

theorem cRk_closure_congr (hXY : M.closure X = M.closure Y) : M.cRk X = M.cRk Y := by
  rw [← cRk_closure, hXY, cRk_closure]

theorem Spanning.cRank_le_cardinalMk (h : M.Spanning X) : M.cRank ≤ #X :=
  have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  (hB.cardinalMk_eq_cRank).symm.trans_le (mk_le_mk_of_subset hBX)

variable (M : Matroid α) [InvariantCardinalRank M] (e : α) (X Y : Set α)

@[simp] theorem cRk_union_closure_right_eq : M.cRk (X ∪ M.closure Y) = M.cRk (X ∪ Y) :=
  M.cRk_closure_congr (M.closure_union_closure_right_eq _ _)

@[simp] theorem cRk_union_closure_left_eq : M.cRk (M.closure X ∪ Y) = M.cRk (X ∪ Y) :=
  M.cRk_closure_congr (M.closure_union_closure_left_eq _ _)

@[simp] theorem cRk_insert_closure_eq : M.cRk (insert e (M.closure X)) = M.cRk (insert e X) := by
  rw [← union_singleton, cRk_union_closure_left_eq, union_singleton]

theorem cRk_union_closure_eq : M.cRk (M.closure X ∪ M.closure Y) = M.cRk (X ∪ Y) := by
  simp

/-- The `Cardinal` rank function is submodular. -/
theorem cRk_inter_add_cRk_union_le : M.cRk (X ∩ Y) + M.cRk (X ∪ Y) ≤ M.cRk X + M.cRk Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_isBasis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← cRk_union_closure_eq, ← hIX.closure_eq_closure, ← hIY.closure_eq_closure,
    cRk_union_closure_eq, ← hIi.cardinalMk_eq_cRk, ← hIX.cardinalMk_eq_cRk,
    ← hIY.cardinalMk_eq_cRk, ← mk_union_add_mk_inter, add_comm]
  exact add_le_add (M.cRk_le_cardinalMk _) (mk_le_mk_of_subset (subset_inter hIX' hIY'))

end Invariant

section Instances

/-- `Finitary` matroids have a cardinality-valued rank function. -/
instance invariantCardinalRank_of_finitary [Finitary M] : InvariantCardinalRank M := by
  suffices aux : ∀ ⦃B B'⦄ ⦃N : Matroid α⦄, Finitary N → N.IsBase B → N.IsBase B' →
      #(B \ B' : Set α) ≤ #(B' \ B : Set α) from
    ⟨fun I J X hI hJ ↦ (aux (restrict_finitary X) hI.isBase_restrict hJ.isBase_restrict).antisymm
      (aux (restrict_finitary X) hJ.isBase_restrict hI.isBase_restrict)⟩
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

instance invariantCardinalRank_map (M : Matroid α) [InvariantCardinalRank M] (hf : InjOn f M.E) :
    InvariantCardinalRank (M.map f hf) := by
  refine ⟨fun I J X hI hJ ↦ ?_⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := map_isBasis_iff'.1 hI
  obtain ⟨J, X', hJX, rfl, h'⟩ := map_isBasis_iff'.1 hJ
  obtain rfl : X = X' := by
    rwa [InjOn.image_eq_image_iff hf hIX.subset_ground hJX.subset_ground] at h'
  have hcard := hIX.cardinalMk_diff_comm hJX
  rwa [← lift_inj.{u,v},
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hIX.indep.diff _).subset_ground)),
    ← mk_image_eq_of_injOn_lift _ _ (hf.mono ((hJX.indep.diff _).subset_ground)),
    lift_inj, (hf.mono hIX.indep.subset_ground).image_diff,
    (hf.mono hJX.indep.subset_ground).image_diff, inter_comm,
    hf.image_inter hJX.indep.subset_ground hIX.indep.subset_ground,
    diff_inter_self_eq_diff, diff_self_inter] at hcard

instance invariantCardinalRank_comap (M : Matroid β) [InvariantCardinalRank M] (f : α → β) :
    InvariantCardinalRank (M.comap f) := by
  refine ⟨fun I J X hI hJ ↦ ?_⟩
  obtain ⟨hI, hfI, hIX⟩ := comap_isBasis_iff.1 hI
  obtain ⟨hJ, hfJ, hJX⟩ := comap_isBasis_iff.1 hJ
  rw [← lift_inj.{u,v}, ← mk_image_eq_of_injOn_lift _ _ (hfI.mono diff_subset),
    ← mk_image_eq_of_injOn_lift _ _ (hfJ.mono diff_subset), lift_inj, hfI.image_diff,
    hfJ.image_diff, ← diff_union_diff_cancel inter_subset_left (image_inter_subset f I J),
    inter_comm, diff_inter_self_eq_diff, mk_union_of_disjoint, hI.cardinalMk_diff_comm hJ,
    ← diff_union_diff_cancel inter_subset_left (image_inter_subset f J I), inter_comm,
    diff_inter_self_eq_diff, mk_union_of_disjoint, inter_comm J I] <;>
  exact disjoint_sdiff_left.mono_right (diff_subset.trans inter_subset_left)

end Instances

theorem rankFinite_iff_cRank_lt_aleph0 : M.RankFinite ↔ M.cRank < ℵ₀ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · have ⟨B, hB, fin⟩ := h
    exact hB.cardinalMk_eq_cRank ▸ lt_aleph0_iff_finite.mpr fin
  have ⟨B, hB⟩ := M.exists_isBase
  simp_rw [← finite_coe_iff, ← lt_aleph0_iff_finite]
  exact ⟨B, hB, hB.cardinalMk_le_cRank.trans_lt h⟩

theorem rankInfinite_iff_aleph0_le_cRank : M.RankInfinite ↔ ℵ₀ ≤ M.cRank := by
  rw [← not_lt, ← rankFinite_iff_cRank_lt_aleph0, not_rankFinite_iff]

theorem isRkFinite_iff_cRk_lt_aleph0 : M.IsRkFinite X ↔ M.cRk X < ℵ₀ := by
  rw [IsRkFinite, rankFinite_iff_cRank_lt_aleph0, cRank_restrict]

theorem Indep.isBase_of_cRank_le [M.RankFinite] (ind : M.Indep I) (le : M.cRank ≤ #I) :
    M.IsBase I :=
  ind.isBase_of_maximal fun _J ind_J hIJ ↦ ind.finite.eq_of_subset_of_encard_le hIJ <|
    toENat.monotone' <| ind_J.cardinalMk_le_cRank.trans le

theorem Spanning.isBase_of_le_cRank [M.RankFinite] (h : M.Spanning X) (le : #X ≤ M.cRank) :
    M.IsBase X := by
  have ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  rwa [← hB.finite.eq_of_subset_of_encard_le hBX
    (toENat.monotone' <| le.trans hB.cardinalMk_eq_cRank.ge)]

theorem Indep.isBase_of_cRank_le_of_finite (ind : M.Indep I)
    (le : M.cRank ≤ #I) (fin : I.Finite) : M.IsBase I :=
  have := rankFinite_iff_cRank_lt_aleph0.mpr (le.trans_lt <| lt_aleph0_iff_finite.mpr fin)
  ind.isBase_of_cRank_le le

theorem Spanning.isBase_of_le_cRank_of_finite (h : M.Spanning X)
    (le : #X ≤ M.cRank) (fin : X.Finite) : M.IsBase X :=
  have ⟨_B, hB, hBX⟩ := h.exists_isBase_subset
  have := hB.rankFinite_of_finite (fin.subset hBX)
  h.isBase_of_le_cRank le

@[simp]
theorem toENat_cRank_eq (M : Matroid α) : M.cRank.toENat = M.eRank := by
  obtain h | h := M.rankFinite_or_rankInfinite
  · obtain ⟨B, hB⟩ := M.exists_isBase
    rw [← hB.cardinalMk_eq_cRank, ← hB.encard_eq_eRank, toENat_cardinalMk]
  simp [rankInfinite_iff_aleph0_le_cRank.1 h]

@[simp]
theorem toENat_cRk_eq (M : Matroid α) (X : Set α) : (M.cRk X).toENat = M.eRk X := by
  rw [cRk, toENat_cRank_eq, eRk]

end Matroid
