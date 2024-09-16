/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Discrete
import Mathlib.Order.Interval.Set.WithBotTop

/-!
# Topology on extended natural numbers
-/

open Set

open scoped Topology Filter

namespace ENat

/--
Topology on `ℕ∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, but all neighborhoods of `∞` in `ℕ∞` contain infinite intervals.
-/
instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

@[simp] theorem range_natCast : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe

theorem embedding_natCast : Embedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.embedding_of_ordConnected <| range_natCast ▸ ordConnected_Iio

theorem openEmbedding_natCast : OpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨embedding_natCast, range_natCast ▸ isOpen_Iio⟩

theorem nhds_natCast (n : ℕ) : 𝓝 (n : ℕ∞) = pure (n : ℕ∞) := by
  simp [← openEmbedding_natCast.map_nhds_eq]

@[simp]
protected theorem nhds_eq_pure {n : ℕ∞} (h : n ≠ ⊤) : 𝓝 n = pure n := by
  lift n to ℕ using h
  simp [nhds_natCast]

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  rw [isOpen_singleton_iff_nhds_eq_pure, ENat.nhds_eq_pure hx]

theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  simp [hx]

theorem mem_nhds_natCast_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (coe_ne_top _)

instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.2 fun (a, b) ↦ ?_⟩
  match a, b with
  | ⊤, _ => exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  | (a : ℕ), ⊤ => exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  | (a : ℕ), (b : ℕ) => simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

end ENat
