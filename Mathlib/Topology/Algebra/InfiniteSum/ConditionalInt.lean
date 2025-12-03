/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs


/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used, for
example in the definition of the Eisenstein series `E2`.
In particular we define `symmetricIcc`, `symmetricIco`, `symmetricIoc` and `symmetricIoo` as
`SummationFilter`s corresponding to the intervals `Icc -N N`, `Ico -N N`, `Ioc -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

@[expose] public section

open Finset Topology Function Filter SummationFilter

namespace SummationFilter

section IntervalFilters

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G]

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
@[simps]
def symmetricIcc : SummationFilter G where
  filter := atTop.map (fun g ↦ Icc (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioo (-N) N`· Note that for `G = ℤ` this coincides with
`symmetricIcc` so one should use that. See `symmetricIcc_eq_symmetricIoo_int`. -/
@[simps]
def symmetricIoo : SummationFilter G where
  filter := atTop.map (fun g ↦ Ioo (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ico (-N) N`· -/
@[simps]
def symmetricIco : SummationFilter G where
  filter := atTop.map (fun N ↦ Ico (-N) N)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioc (-N) N`· -/
@[simps]
def symmetricIoc : SummationFilter G where
  filter := atTop.map (fun N ↦ Ioc (-N) N)

variable [(atTop : Filter G).NeBot]

instance : (symmetricIcc G).NeBot where
  ne_bot := by simp [symmetricIcc, Filter.NeBot.map]

instance : (symmetricIco G).NeBot where
  ne_bot := by simp [symmetricIco, Filter.NeBot.map]

instance : (symmetricIoc G).NeBot where
  ne_bot := by simp [symmetricIoc, Filter.NeBot.map]

instance : (symmetricIoo G).NeBot where
  ne_bot := by simp [symmetricIoo, Filter.NeBot.map]

section LeAtTop

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

lemma symmetricIcc_le_Conditional :
    (symmetricIcc G).filter ≤ (conditional G).filter :=
  Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)

instance : (symmetricIcc G).LeAtTop where
  le_atTop := le_trans symmetricIcc_le_Conditional (conditional G).le_atTop

variable [NoTopOrder G] [NoBotOrder G]

instance : (symmetricIco G).LeAtTop where
  le_atTop := by
    rw [symmetricIco, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ico_neg_atTop_atTop

instance : (symmetricIoc G).LeAtTop where
  le_atTop := by
    rw [symmetricIoc, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioc_neg_atTop_atTop

instance : (symmetricIoo G).LeAtTop where
  le_atTop := by
    rw [symmetricIoo, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioo_neg_atTop_atTop

end LeAtTop

end IntervalFilters
section Int

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

lemma symmetricIcc_eq_map_Icc_nat :
    (symmetricIcc ℤ).filter = atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N) := by
  simp [← Nat.map_cast_int_atTop, Function.comp_def]

lemma symmetricIcc_eq_symmetricIoo_int : symmetricIcc ℤ = symmetricIoo ℤ := by
  simp only [symmetricIcc, symmetricIoo, mk.injEq]
  ext s
  simp only [← Nat.map_cast_int_atTop, Filter.map_map, Filter.mem_map, mem_atTop_sets, ge_iff_le,
    Set.mem_preimage, comp_apply]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a + 1, fun b hb ↦ ?_⟩, fun ⟨a, ha⟩ ↦ ⟨a - 1, fun b hb ↦ ?_⟩⟩ <;>
  [ convert ha (b - 1) (by grind) using 1; convert ha (b + 1) (by grind) using 1 ] <;>
  simpa [Finset.ext_iff] using by grind

@[to_additive]
lemma HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc {a : α}
    (hf : HasProd f a (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    HasProd f a (symmetricIco ℤ) := by
  simp only [HasProd, tendsto_map'_iff, symmetricIcc_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, symmetricIco] at *
  apply tendsto_of_div_tendsto_one _ hf
  simpa [Pi.div_def, fun N : ℕ ↦ prod_Icc_eq_prod_Ico_mul f (show (-N : ℤ) ≤ N by omega)]
    using hf2

@[to_additive]
lemma multipliable_symmetricIco_of_multiplible_symmetricIcc
    (hf : Multipliable f (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    Multipliable f (symmetricIco ℤ) :=
  (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).multipliable

@[to_additive]
lemma tprod_symmetricIcc_eq_tprod_symmetricIco [T2Space α]
    (hf : Multipliable f (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[symmetricIco ℤ] b, f b = ∏'[symmetricIcc ℤ] b, f b :=
  (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).tprod_eq

@[to_additive]
lemma hasProd_symmetricIcc_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIcc ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Icc (-(N : ℤ)) N, f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIcc, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
lemma hasProd_symmetricIco_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIco ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Ico (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIco, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
lemma hasProd_symmetricIoc_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIoc ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Ioc (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIoc, ← Nat.map_cast_int_atTop, comp_def]

end Int

end SummationFilter
