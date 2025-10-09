/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star

/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used in the
definition of the Eisenstein series `E2`. In particular we define `IccFilter`, `IcoFilter`,
`IocFilter` and `IooFilter` as `SummationFilter`s on `Finset ℤ` corresponding to the intervals
`Icc -N N`, `Ico -N N`, `Ioc -N N` and `Ioo -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

open Finset Topology

lemma Icc_succ_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n + 1) : ℤ), (n + 1 : ℤ)} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega

lemma sum_Icc_of_even_eq_range {α : Type*} [CommRing α] {f : ℤ → α} (hf : ∀ n, f n = f (-n))
    (N : ℕ) : ∑ m ∈  Finset.Icc (-N : ℤ) N, f m =  2 * ∑ m ∈ Finset.range (N + 1), f m - f 0 := by
  induction N with
  | zero => simp [two_mul]
  | succ N ih =>
    have := Icc_succ_succ N
    simp only [neg_add_rev, Int.reduceNeg,  Nat.cast_add, Nat.cast_one] at *
    rw [this, Finset.sum_union (by simp), Finset.sum_pair (by omega), ih]
    nth_rw 2 [Finset.sum_range_succ]
    grind

@[to_additive]
lemma prod_Icc_eq_prod_Ico_succ {α : Type*} [CommMonoid α] (f : ℤ → α) {l u : ℤ} (h : l ≤ u) :
    ∏ m ∈ Icc l u, f m = (∏ m ∈ Finset.Ico l u, f m) * f u := by
  simp [Finset.Icc_eq_cons_Ico h,Finset.cons_eq_insert, Finset.mem_Ico, lt_self_iff_false, mul_comm]

lemma sum_Icc_add_endpoints {R : Type*} [AddCommGroup R] (f : ℤ → R) {N : ℕ} (hn : 1 ≤ N) :
    ∑ m ∈ Icc (-N : ℤ) N, f m = f N + f (-N : ℤ)  + ∑ m ∈ Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N
  · grind
  · zify
    rw [Icc_succ_succ, Finset.sum_union (by simp)]
    grind

section IntervalFilters

open TopologicalSpace Filter Function Finset

lemma Finset.tendsto_Icc_atTop_atTop : Tendsto (fun N : ℕ ↦ Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma Finset.tendsto_Ico_atTop_atTop : Tendsto (fun N : ℕ ↦ Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  exact fun x ↦ ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    Int.lt_add_one_iff.mpr (le_abs_self x)⟩ ⟩

lemma Finset.tendsto_Ioc_atTop_atTop : Tendsto (fun N : ℕ ↦ Finset.Ioc (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioc_subset_Ioc (by omega) (by gcongr))
  exact fun x ↦ ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x)).le⟩⟩

lemma Finset.tendsto_Ioo_atTop_atTop : Tendsto (fun N : ℕ ↦ Finset.Ioo (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioo_subset_Ioo (by omega) (by gcongr))
  exact fun x ↦ ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x))⟩⟩

/-- The SummationFilter on `Finset ℤ` corresponding to the intervals `Icc (-N) N` -/
abbrev IccFilter : SummationFilter ℤ where
  filter := atTop.map (fun N : ℕ ↦ Finset.Icc (-(N : ℤ)) N)

/-- The SummationFilter on `Finset ℤ` corresponding to the intervals `Ico (-N) N` -/
abbrev IcoFilter : SummationFilter ℤ where
  filter := atTop.map (fun N : ℕ ↦ Ico (-(N : ℤ)) N)

/-- The SummationFilter on `Finset ℤ` corresponding to the intervals `Ioc (-N) N` -/
abbrev IocFilter : SummationFilter ℤ where
  filter := atTop.map (fun N : ℕ ↦ Ioc (-(N : ℤ)) N)

/-- The SummationFilter on `Finset ℤ` corresponding to the intervals `Ioo (-N) N` -/
abbrev IooFilter : SummationFilter ℤ where
  filter := atTop.map (fun N : ℕ ↦ Ioo (-(N : ℤ)) N)

instance IccFilter_neBot : NeBot (atTop.map (fun N : ℕ ↦ Finset.Icc (-(N : ℤ)) N)) := by
  simp [Filter.NeBot.map]

instance IcoFilter_neBot : NeBot (atTop.map (fun N : ℕ ↦ Finset.Ico (-(N : ℤ)) N)) := by
  simp [Filter.NeBot.map]

instance IocFilter_neBot : NeBot (atTop.map (fun N : ℕ ↦ Finset.Ioc (-(N : ℤ)) N)) := by
  simp [Filter.NeBot.map]

instance IooFilter_neBot : NeBot (atTop.map (fun N : ℕ ↦ Finset.Ioo (-(N : ℤ)) N)) := by
  simp [Filter.NeBot.map]

lemma IccFilter_le_atTop : atTop.map (fun N : ℕ ↦ Finset.Icc (-(N : ℤ)) N) ≤ atTop := by
  rw [@map_le_iff_le_comap, ← @tendsto_iff_comap]
  exact Finset.tendsto_Icc_atTop_atTop

lemma IcoFilter_le_atTop : atTop.map (fun N : ℕ ↦ Finset.Ico (-(N : ℤ)) N) ≤ atTop := by
  rw [@map_le_iff_le_comap, ← @tendsto_iff_comap]
  exact Finset.tendsto_Ico_atTop_atTop

lemma IocFilter_le_atTop : atTop.map (fun N : ℕ ↦ Finset.Ioc (-(N : ℤ)) N) ≤ atTop := by
  rw [@map_le_iff_le_comap, ← @tendsto_iff_comap]
  exact Finset.tendsto_Ioc_atTop_atTop

lemma IooFilter_le_atTop : atTop.map (fun N : ℕ ↦ Finset.Ioo (-(N : ℤ)) N) ≤ atTop := by
  rw [@map_le_iff_le_comap, ← @tendsto_iff_comap]
  exact Finset.tendsto_Ioo_atTop_atTop

instance : (IccFilter).NeBot := ⟨IccFilter_neBot⟩

instance : (IcoFilter).NeBot := ⟨IcoFilter_neBot⟩

instance : (IocFilter).NeBot := ⟨IocFilter_neBot⟩

instance : (IooFilter).NeBot := ⟨IooFilter_neBot⟩

instance : (IccFilter).LeAtTop where
  le_atTop := IccFilter_le_atTop

instance : (IcoFilter).LeAtTop where
  le_atTop := IcoFilter_le_atTop

instance : (IocFilter).LeAtTop where
  le_atTop := IocFilter_le_atTop

instance : (IooFilter).LeAtTop where
  le_atTop := IooFilter_le_atTop

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

@[to_additive]
lemma multipliable_IcoFilter_of_multiplible_IccFilter (hf : Multipliable f IccFilter)
    (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) : Multipliable f IcoFilter := by
  have := (hf.hasProd)
  apply HasProd.multipliable (a := ∏'[IccFilter] (b : ℤ), f b)
  simp only [HasProd, tendsto_map'_iff] at *
  apply Filter.Tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

@[to_additive]
lemma tprod_IccFilter_eq_tprod_IcoFilter [T2Space α] (hf : Multipliable f IccFilter)
    (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[IccFilter] b, f b  = ∏'[IcoFilter] b, f b := by
  have := (hf.hasProd)
  apply symm
  apply HasProd.tprod_eq
  simp only [HasProd, tendsto_map'_iff] at *
  apply Filter.Tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

section tprod

variable {α : Type*} [CommMonoid α] [TopologicalSpace α] [T2Space α]

@[to_additive]
lemma tprod_IccFilter_eq_tprod {f : ℤ → α} (hf : Multipliable f) :
    ∏'[IccFilter] b, f b = ∏' b, f b  := by
  apply HasProd.tprod_eq
  apply ((hf.hasProd).comp Finset.tendsto_Icc_atTop_atTop).congr
  simp

@[to_additive]
lemma tprod_IcoFilter_eq_tprod {f : ℤ → α} (hf : Multipliable f) :
     ∏'[IcoFilter] b, f b = ∏' b, f b  := by
  apply HasProd.tprod_eq
  apply ((hf.hasProd).comp Finset.tendsto_Ico_atTop_atTop).congr
  simp

@[to_additive]
lemma tprod_IocFilter_eq_tprod {f : ℤ → α} (hf : Multipliable f) :
     ∏'[IocFilter] b, f b = ∏' b, f b  := by
  apply HasProd.tprod_eq
  apply ((hf.hasProd).comp Finset.tendsto_Ioc_atTop_atTop).congr
  simp

@[to_additive]
lemma tprod_IooFilter_eq_tprod {f : ℤ → α} (hf : Multipliable f) :
     ∏'[IooFilter] b, f b = ∏' b, f b  := by
  apply HasProd.tprod_eq
  apply ((hf.hasProd).comp Finset.tendsto_Ioo_atTop_atTop).congr
  simp

end tprod

end IntervalFilters
