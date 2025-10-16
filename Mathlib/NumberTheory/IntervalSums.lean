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
import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used in the
definition of the Eisenstein series `E2`. In particular we define `SymmetricConditional`,
`IcoFilter`, `IocFilter` as `SummationFilter`s  corresponding to the intervals
`Icc -N N`, `Ico -N N`, `Ioc -N N` respectively.
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

open Filter Function Finset SummationFilter

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G]

/-- The SummationFilter on Locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
def SummationFilter.symmetricConditional :
    SummationFilter G where
  filter := atTop.map (fun g ↦ Icc (-g) g)

/-- The SummationFilter on `ℤ` corresponding to the intervals `Icc -N N`. Note that this is
the same as the limit over open intervals `Ioo -N N` (see `SymmetricConditional_eq_map_Ioo`). -/
abbrev SummationFilter.symCondInt : SummationFilter ℤ :=
  SummationFilter.symmetricConditional ℤ

lemma SymmetricConditional_eq_map_Icc :
    symCondInt.filter = atTop.map (fun N ↦ Icc (-N) N) := rfl

lemma SymmetricConditional_eq_map_Icc_nat :
    symCondInt.filter = atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N) := by
  rw [symCondInt, symmetricConditional, ← Nat.map_cast_int_atTop]
  rfl

/-- The SummationFilter on `G` corresponding to the intervals `Ico (-N) N`. -/
def SummationFilter.IcoFilter : SummationFilter G where
  filter := atTop.map (fun N ↦ Ico (-N) N)

/-- The SummationFilter on `G` corresponding to the intervals `Ioc (-N) N`. -/
def SummationFilter.IocFilter : SummationFilter G where
  filter := atTop.map (fun N ↦ Ioc (-N) N)

lemma SymmetricConditional_eq_map_Ioo :
    (symmetricConditional ℤ).filter = atTop.map (fun N ↦ Ioo (-(N : ℤ)) N) := by
  rw [symmetricConditional, ← Nat.map_cast_int_atTop]
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
    rw [mem_Icc, mem_Ioo]
    grind

variable [(atTop : Filter G).NeBot]

instance : (symmetricConditional G).NeBot where
  ne_bot := by simp [symmetricConditional, Filter.NeBot.map]

instance : (IcoFilter G).NeBot where
  ne_bot := by simp [IcoFilter, Filter.NeBot.map]

instance : (IocFilter G).NeBot where
  ne_bot := by simp [IocFilter, Filter.NeBot.map]

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

-- This proof was basically done by Aristotle
lemma SymmetricConditional_le_Conditional :
    (symmetricConditional G).filter ≤ (conditional G).filter := by
  simp only [symmetricConditional, map_le_iff_le_comap, ← @tendsto_iff_comap, conditional]
  suffices  Tendsto (fun g : G ↦ (-g, g)) atTop (atBot ×ˢ atTop) by
    exact Filter.map_mono this
  exact Filter.Tendsto.prodMk tendsto_neg_atTop_atBot (tendsto_id)

instance : (symmetricConditional G).LeAtTop where
  le_atTop := le_trans SymmetricConditional_le_Conditional (conditional G).le_atTop

instance : (IcoFilter ℤ).LeAtTop where
  le_atTop := by
    rw [IcoFilter, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ico_atTop_atTop

instance : (IocFilter ℤ).LeAtTop where
  le_atTop := by
    rw [IocFilter, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioc_atTop_atTop

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

@[to_additive]
lemma multipliable_IcoFilter_of_multiplible_SymmetricConditional
    (hf : Multipliable f symCondInt) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    Multipliable f (IcoFilter ℤ) := by
  have := (hf.hasProd)
  apply HasProd.multipliable (a := ∏'[symCondInt] (b : ℤ), f b)
  simp only [HasProd, tendsto_map'_iff, SymmetricConditional_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, IcoFilter] at *
  apply Filter.Tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

@[to_additive]
lemma tprod_SymmetricConditional_eq_tprod_IcoFilter [T2Space α]
    (hf : Multipliable f symCondInt) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[symCondInt] b, f b = ∏'[IcoFilter ℤ] b, f b := by
  have := (hf.hasProd)
  apply symm
  apply HasProd.tprod_eq
  simp only [HasProd, tendsto_map'_iff, SymmetricConditional_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, IcoFilter] at *
  apply Filter.Tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

end IntervalFilters
