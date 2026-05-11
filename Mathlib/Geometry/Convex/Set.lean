/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs

import Mathlib.Data.Fintype.Order

/-!
# Convex sets

This file defines convex sets in a convex space.

## Implementation notes

To allow full generality on the coefficients, for `s` to be convex we require that all finitary
convex combinations of points of `s` lie in `s`, instead of merely binary ones as is customary.

Since its body is an implementation detail, the predicate `IsConvexSet` is unexposed.

## TODO

Prove that cartesian products of convex sets are convex.
-/

namespace Finsupp
variable {α M N : Type*} [AddCommMonoid M] [CommMonoid N]

@[to_additive (attr := simp)]
lemma prod_onFinset (s : Finset α) (f : α → M) (hf) (g : α → M → N) (hg : ∀ i ∈ s, g i 0 = 1) :
    (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a) :=
  prod_of_support_subset _ support_onFinset_subset _ hg

end Finsupp

open Finsupp Set

public section

namespace Convexity
variable {ι R K X Y : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X → Y} {w : StdSimplex R X} {s t : Set X} {x y : X}

variable (R s) in
/-- A set `s` in a convex space is convex if all convex combinations of points in `s` lie themselves
in `s`.

When the scalars form a field, this is equivalent to the definition in terms of binary combinations.
See `IsConvexSet.of_convexComboPair_mem`. -/
def IsConvexSet : Prop := ∀ ⦃w : StdSimplex R X⦄, ↑w.weights.support ⊆ s → w.sConvexCombo ∈ s

lemma IsConvexSet.of_sConvexCombo_mem
    (hs : ∀ w : StdSimplex R X, ↑w.weights.support ⊆ s → w.sConvexCombo ∈ s) : IsConvexSet R s :=
  hs

lemma IsConvexSet.sConvexCombo_mem (hs : IsConvexSet R s) (hw : ↑w.weights.support ⊆ s) :
    w.sConvexCombo ∈ s := hs hw

lemma IsConvexSet.iConvexCombo_mem (hs : IsConvexSet R s) {w : StdSimplex R ι} {f : ι → X}
    (hf : ∀ i, w.weights i ≠ 0 → f i ∈ s) : w.iConvexCombo f ∈ s := by
  classical
  refine hs ?_
  grw [StdSimplex.weights_map, mapDomain_support]
  simpa [subset_def]

lemma IsConvexSet.convexComboPair_mem (hs : IsConvexSet R s) (hx : x ∈ s) (hy : y ∈ s)
    {a b : R} (ha hb hab) : convexComboPair a b ha hb hab x y ∈ s := by
  classical
  refine hs.sConvexCombo_mem ?_
  grw [StdSimplex.weights_duple, support_add, support_single_subset, support_single_subset]
  simp [*, insert_subset_iff]

@[simp] protected lemma IsConvexSet.empty : IsConvexSet R (∅ : Set X) := by simp [IsConvexSet]
@[simp] protected lemma IsConvexSet.univ : IsConvexSet R (.univ : Set X) := by simp [IsConvexSet]

@[simp] protected lemma IsConvexSet.singleton : IsConvexSet R {x} := by
  simp [IsConvexSet, -subset_singleton_iff, Finset.coe_subset_singleton]

lemma IsConvexSet.of_subsingleton (hs : s.Subsingleton) : IsConvexSet R s := by
  obtain rfl | ⟨x, rfl⟩ := hs.eq_empty_or_singleton <;> simp

protected lemma IsConvexSet.inter (hs : IsConvexSet R s) (ht : IsConvexSet R t) :
    IsConvexSet R (s ∩ t) := by
  simp +contextual [IsConvexSet, hs.sConvexCombo_mem, ht.sConvexCombo_mem]

protected lemma IsConvexSet.sInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsConvexSet R s) :
    IsConvexSet R (⋂₀ S) := by simp +contextual [IsConvexSet, (hS _ _).sConvexCombo_mem]

protected lemma IsConvexSet.iInter {ι : Sort*} {s : ι → Set X} (hs : ∀ i, IsConvexSet R (s i)) :
    IsConvexSet R (⋂ i, s i) := by simp +contextual [IsConvexSet, (hs _).sConvexCombo_mem]

lemma IsConvexSet.iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : ∀ i, κ i → Set X}
    (h : ∀ i j, IsConvexSet R (s i j)) : IsConvexSet R (⋂ (i) (j), s i j) :=
  .iInter fun i ↦ .iInter <| h i

protected lemma IsConvexSet.sUnion {S : Set (Set X)} (hS : DirectedOn (· ⊆ ·) S)
    (hS' : ∀ s ∈ S, IsConvexSet R s) : IsConvexSet R (⋃₀ S) := by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  rintro w hw
  obtain ⟨s, hsS, hws⟩ :=
    hS.exists_mem_subset_of_finite_of_subset_sUnion hS'' w.weights.support.finite_toSet hw
  exact mem_sUnion_of_mem (hS' s hsS hws) hsS

protected lemma IsConvexSet.iUnion {ι : Sort*} {s : ι → Set X} (hs : Directed (· ⊆ ·) s)
    (hs' : ∀ i, IsConvexSet R (s i)) : IsConvexSet R (⋃ i, s i) :=
  .sUnion hs.directedOn_range <| by simpa

protected lemma IsConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f) (hs : IsConvexSet R s) :
    IsConvexSet R (f ⁻¹' s) := by
  classical
  rintro w hw
  simp only [mem_preimage, hf.map_sConvexCombo, sConvexCombo_map]
  exact hs.iConvexCombo_mem fun x hx ↦ hw <| by simpa

protected lemma IsConvexSet.image (hf : IsAffineMap R f) (hs : IsConvexSet R s) :
    IsConvexSet R (f '' s) := by
  classical
  rintro w hw
  obtain ⟨u, hus, hfu, huw⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hw
  refine ⟨sConvexCombo {
      weights := .onFinset u (fun x ↦ if x ∈ u then w.weights (f x) else 0) <| by simp +contextual
      nonneg x := by simp; split <;> simp
      total := by
        simp only [implies_true, sum_onFinset, Finset.sum_ite_mem, Finset.inter_self,
        ← Finset.sum_image hfu, huw]
        exact w.total
    }, hs.sConvexCombo_mem <| by grw [support_onFinset_subset, hus], ?_⟩
  rw [hf.map_sConvexCombo]
  congr
  ext y
  rw [StdSimplex.weights_map]
  by_cases hy : y ∈ w.weights.support
  · rw [← huw, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    convert mapDomain_apply' _ _ support_onFinset_subset hfu hx
    exact (if_pos hx).symm
  · rw [mapDomain_of_not_mem_image_support (by simp [← huw] at ⊢ hy; tauto)]
    simp_all

end Semiring

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}

/-- Convexity of a set can be checked via binary combinations if the scalars form a field. -/
lemma IsConvexSet.of_convexComboPair_mem
    (hs : ∀ a b : K, ∀ ha hb hab, ∀ x ∈ s, ∀ y ∈ s, convexComboPair a b ha hb hab x y ∈ s) :
    IsConvexSet K s := by
  classical
  rintro w hw
  set t := w.weights.support with hsw
  have ht : t.Nonempty := w.support_weights_nonempty
  clear_value t
  induction ht using Finset.Nonempty.cons_induction generalizing w with
  | singleton x => simp_all [eq_comm]
  | cons x t hx ht ih =>
  have hwx : w.weights x ≠ 0 := by simpa using congr(x ∈ $hsw)
  have hwx' : ∃ y ≠ x, w.weights y ≠ 0 := by
    obtain ⟨y, hy⟩ := ht
    exact ⟨y, ne_of_mem_of_not_mem hy hx, by simpa [hy] using congr(y ∈ $hsw)⟩
  rw [← w.convexComboPair_restrict_restrict_compl {x} (by simpa) hwx']
  simp only [mem_singleton_iff, StdSimplex.restrict_singleton, sConvexCombo_convexComboPair,
    sConvexCombo_single]
  exact hs _ _ _ _ _ _ (hw <| by simp) _ <| ih (by grw [← hw, ← Finset.subset_cons])
    (by simp [← hsw]; grind)

end Field
end Convexity
