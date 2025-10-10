/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used in the
definition of the Eisenstein series `E2`. In particular we define `IccFilter`, `IcoFilter`,
`IocFilter` and `IooFilter` as `SummationFilter`s on `ℤ` corresponding to the intervals
`Icc -N N`, `Ico -N N`, `Ioc -N N` and `Ioo -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

open Finset Topology

--Should this go elsewhere?
lemma Finset.Icc_succ_succ (n : ℕ) : Icc (-(n + 1) : ℤ) (n + 1) = Icc (-n : ℤ) n ∪
  {(-(n + 1) : ℤ), (n + 1 : ℤ)} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  simp only [neg_add_rev, Int.reduceNeg, mem_Icc, add_neg_le_iff_le_add, union_insert,
    union_singleton, mem_insert]
  omega

lemma Finset.sum_Icc_of_even_eq_range {α : Type*} [CommRing α] {f : ℤ → α} (hf : ∀ n, f n = f (-n))
    (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, f m = 2 * ∑ m ∈ range (N + 1), f m - f 0 := by
  induction N with
  | zero => simp [two_mul]
  | succ N ih =>
    have := Icc_succ_succ N
    simp only [neg_add_rev, Int.reduceNeg, Nat.cast_add, Nat.cast_one] at *
    rw [this, sum_union (by simp), sum_pair (by omega), ih]
    nth_rw 2 [sum_range_succ]
    grind

@[to_additive]
lemma Finset.prod_Icc_eq_prod_Ico_succ {α : Type*} [CommMonoid α] (f : ℤ → α) {l u : ℤ}
    (h : l ≤ u) : ∏ m ∈ Icc l u, f m = (∏ m ∈ Ico l u, f m) * f u := by
  simp only [Icc_eq_cons_Ico h, cons_eq_insert, mem_Ico, lt_self_iff_false, and_false,
    not_false_eq_true, prod_insert, mul_comm]

lemma Finset.sum_Icc_add_endpoints {R : Type*} [AddCommGroup R] (f : ℤ → R) {N : ℕ} (hn : 1 ≤ N) :
    ∑ m ∈ Icc (-N : ℤ) N, f m = f N + f (-N : ℤ) + ∑ m ∈ Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N
  · grind
  · zify
    rw [Icc_succ_succ, sum_union (by simp)]
    grind

section IntervalFilters

open TopologicalSpace Filter Function Finset SummationFilter

lemma Finset.tendsto_Icc_atTop_atTop : Tendsto (fun N : ℕ ↦ Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma Finset.tendsto_Ico_atTop_atTop : Tendsto (fun N : ℕ ↦ Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Ico_subset_Ico (by omega) (by gcongr))
  exact fun x ↦ ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    Int.lt_add_one_iff.mpr (le_abs_self x)⟩ ⟩

lemma Finset.tendsto_Ioc_atTop_atTop : Tendsto (fun N : ℕ ↦ Ioc (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Ioc_subset_Ioc (by omega) (by gcongr))
  exact fun x ↦ ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x)).le⟩⟩

lemma Finset.tendsto_Ioo_atTop_atTop : Tendsto (fun N : ℕ ↦ Ioo (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Ioo_subset_Ioo (by omega) (by gcongr))
  exact fun x ↦ ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x))⟩⟩

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G] [(atTop : Filter G).NeBot]

/-- The SummationFilter on Locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
def SummationFilter.SymmetricConditional :
    SummationFilter G where
  filter := atTop.map (fun g ↦ Icc (-g) g)

abbrev SummationFilter.IccFilter : SummationFilter ℤ :=
  SummationFilter.SymmetricConditional ℤ

lemma SymmetricConditional_eq_map_Icc :
    IccFilter.filter = atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N) := by
  rw [IccFilter, SymmetricConditional, ← Nat.map_cast_int_atTop]
  rfl

/-- The SummationFilter on `ℤ` corresponding to the intervals `Ico (-N) N`. -/
abbrev SummationFilter.IcoFilter : SummationFilter ℤ where
  filter := atTop.map (fun N : ℕ ↦ Ico (-(N : ℤ)) N)

/-- The SummationFilter on `ℤ` corresponding to the intervals `Ioc (-N) N`. -/
abbrev SummationFilter.IocFilter : SummationFilter ℤ where
  filter := atTop.map (fun N : ℕ ↦ Ioc (-(N : ℤ)) N)

lemma SymmetricConditional_eq_map_Ioo :
    (SymmetricConditional ℤ).filter = atTop.map (fun N : ℕ ↦ Ioo (-(N : ℤ)) N) := by
  rw [SymmetricConditional, ← Nat.map_cast_int_atTop]
  ext s
  simp only [Filter.mem_map, mem_atTop_sets, ge_iff_le, Set.mem_preimage]
  constructor
  · intro ⟨a, ha⟩
    refine ⟨a + 1, fun b hb ↦ ?_⟩
    convert ha (b - 1) (by grind) using 1
    ext x
    rw [mem_Ioo, mem_Icc]
    grind
  · intro ⟨a, ha⟩
    refine ⟨a - 1, fun b hb ↦ ?_⟩
    convert ha (b + 1) (by grind) using 1
    ext x
    simp only [mem_Icc, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg, mem_Ioo,
      add_neg_lt_iff_lt_add]
    grind

instance : (SymmetricConditional G).NeBot where
  ne_bot := by simp [SymmetricConditional, Filter.NeBot.map]

instance : (IcoFilter).NeBot where
  ne_bot := by simp [Filter.NeBot.map]

instance : (IocFilter).NeBot where
  ne_bot := by simp [Filter.NeBot.map]

instance : IccFilter.LeAtTop where
  le_atTop := by
    rw [SymmetricConditional_eq_map_Icc, @map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Icc_atTop_atTop

instance : (IcoFilter).LeAtTop where
  le_atTop := by
    rw [@map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ico_atTop_atTop

instance : (IocFilter).LeAtTop where
  le_atTop := by
    rw [@map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioc_atTop_atTop

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

@[to_additive]
lemma multipliable_IcoFilter_of_multiplible_SymmetricConditional
    (hf : Multipliable f IccFilter) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    Multipliable f IcoFilter := by
  have := (hf.hasProd)
  apply HasProd.multipliable (a := ∏'[IccFilter] (b : ℤ), f b)
  simp only [HasProd, tendsto_map'_iff, SymmetricConditional_eq_map_Icc] at *
  apply Filter.Tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

@[to_additive]
lemma tprod_SymmetricConditional_eq_tprod_IcoFilter [T2Space α]
    (hf : Multipliable f IccFilter) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[IccFilter] b, f b = ∏'[IcoFilter] b, f b := by
  have := (hf.hasProd)
  apply symm
  apply HasProd.tprod_eq
  simp only [HasProd, tendsto_map'_iff, SymmetricConditional_eq_map_Icc] at *
  apply Filter.Tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

end IntervalFilters
