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
import Mathlib.Algebra.Group.EvenFunction

/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used in the
definition of the Eisenstein series `E2`. In particular we define `SymmetricConditional`,
`IcoFilter`, `IocFilter` as `SummationFilter`s  corresponding to the intervals
`Icc -N N`, `Ico -N N`, `Ioc -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

open Finset Topology Function

@[to_additive]
lemma Finset.prod_Icc_of_even_eq_range {α : Type*} [CommGroup α] {f : ℤ → α} (hf : f.Even) (N : ℕ) :
    ∏ m ∈ Icc (-N : ℤ) N, f m = (∏ m ∈ range (N + 1), f m) ^ 2 / f 0 := by
  induction N with
  | zero => simp [sq]
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, Icc_succ_succ, prod_union (by simp), prod_pair (by omega), ih,
      prod_range_succ _ (N + 1), hf, ← pow_two, div_mul_eq_mul_div, ← mul_pow, Nat.cast_succ]

@[to_additive]
lemma Finset.prod_Icc_eq_prod_Ico_succ {α : Type*} [CommMonoid α] (f : ℤ → α) {l u : ℤ}
    (h : l ≤ u) : ∏ m ∈ Icc l u, f m = (∏ m ∈ Ico l u, f m) * f u := by
  simp [Icc_eq_cons_Ico h, mul_comm]

@[to_additive]
lemma Finset.prod_Icc_mul_endpoints {R : Type*} [CommGroup R] (f : ℤ → R) {N : ℕ} (hn : 1 ≤ N) :
    ∏ m ∈ Icc (-N : ℤ) N, f m = f N * f (-N : ℤ) * ∏ m ∈ Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N
  · grind
  · zify
    rw [Icc_succ_succ, prod_union (by simp)]
    grind

section IntervalFilters

open Filter Function Finset SummationFilter

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G]

namespace SummationFilter

/-- The SummationFilter on Locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
def symmetricConditional : SummationFilter G where
  filter := atTop.map (fun g ↦ Icc (-g) g)

/-- The SummationFilter on `ℤ` corresponding to the intervals `Icc -N N`. Note that this is
the same as the limit over open intervals `Ioo -N N` (see `symmetricConditional_eq_map_Ioo`). -/
abbrev symCondInt : SummationFilter ℤ := symmetricConditional ℤ

lemma symmetricConditional_eq_map_Icc :
    (symmetricConditional G).filter = atTop.map (fun N ↦ Icc (-N) N) := rfl

lemma symmetricConditional_eq_map_Icc_nat :
    symCondInt.filter = atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N) := by
  rw [symCondInt, symmetricConditional, ← Nat.map_cast_int_atTop]
  rfl

/-- The SummationFilter on `G` corresponding to the intervals `Ico (-N) N`. -/
def IcoFilter : SummationFilter G where
  filter := atTop.map (fun N ↦ Ico (-N) N)

/-- The SummationFilter on `G` corresponding to the intervals `Ioc (-N) N`. -/
def IocFilter : SummationFilter G where
  filter := atTop.map (fun N ↦ Ioc (-N) N)

lemma symmetricConditional_eq_map_Ioo :
    symCondInt.filter = atTop.map (fun N ↦ Ioo (-N) N) := by
  simp_rw [symmetricConditional, ← Nat.map_cast_int_atTop]
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

section LeAtTop

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

lemma symmetricConditional_le_Conditional :
    (symmetricConditional G).filter ≤ (conditional G).filter :=
  Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)

instance : (symmetricConditional G).LeAtTop where
  le_atTop := le_trans symmetricConditional_le_Conditional (conditional G).le_atTop

instance : (IcoFilter ℤ).LeAtTop where
  le_atTop := by
    rw [IcoFilter, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ico_atTop_atTop

instance : (IocFilter ℤ).LeAtTop where
  le_atTop := by
    rw [IocFilter, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioc_atTop_atTop

end LeAtTop

end SummationFilter

section comparisons

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

@[to_additive]
lemma multipliable_IcoFilter_of_multiplible_symmetricConditional
    (hf : Multipliable f symCondInt) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    Multipliable f (IcoFilter ℤ) := by
  have := (hf.hasProd)
  apply HasProd.multipliable (a := ∏'[symCondInt] (b : ℤ), f b)
  simp only [HasProd, tendsto_map'_iff, symmetricConditional_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, IcoFilter] at *
  apply tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

@[to_additive]
lemma tprod_symmetricConditional_eq_tprod_IcoFilter [T2Space α]
    (hf : Multipliable f symCondInt) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[symCondInt] b, f b = ∏'[IcoFilter ℤ] b, f b := by
  have := (hf.hasProd)
  apply symm
  apply HasProd.tprod_eq
  simp only [HasProd, tendsto_map'_iff, symmetricConditional_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, IcoFilter] at *
  apply tendsto_of_div_tendsto_one _ this
  conv =>
    enter [1, N]
    simp only [Pi.div_apply, comp_apply]
    rw [prod_Icc_eq_prod_Ico_succ _ (by omega)]
  simpa using hf2

@[to_additive]
lemma HasProd_symCondInt_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a symCondInt ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp only [HasProd, symCondInt, symmetricConditional_eq_map_Icc_nat, tendsto_map'_iff]
  rfl

@[to_additive]
lemma HasProd_IcoFilter_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (IcoFilter ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp only [HasProd, IcoFilter, ← Nat.map_cast_int_atTop, Filter.map_map, tendsto_map'_iff]
  rfl

@[to_additive]
lemma HasProd_IocFilter_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (IocFilter ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Finset.Ioc (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp only [HasProd, IocFilter, ← Nat.map_cast_int_atTop, Filter.map_map, tendsto_map'_iff]
  rfl

end comparisons

end IntervalFilters
