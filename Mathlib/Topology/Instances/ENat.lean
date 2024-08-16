/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.ENat.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Discrete

/-!
# Topology on extended natural numbers
-/

open Set Filter
open scoped Topology

namespace ENat

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

instance : ContinuousMul ℕ∞ where
  continuous_mul :=
    have key (a : ℕ∞) : ContinuousAt (· * ·).uncurry (a, ⊤) := by
      rcases (zero_le a).eq_or_gt with rfl | ha
      · simp [ContinuousAt, nhds_prod_eq]
      · simp only [ContinuousAt, Function.uncurry, mul_top ha.ne']
        refine tendsto_nhds_top_mono continuousAt_snd ?_
        filter_upwards [continuousAt_fst (lt_mem_nhds ha)] with (x, y) (hx : 0 < x)
        exact le_mul_of_one_le_left (zero_le y) (ENat.one_le_iff_pos.2 hx)
    continuous_iff_continuousAt.2 <| Prod.forall.2 fun
      | (a : ℕ∞), ⊤ => key a
      | ⊤, (b : ℕ∞) =>
        ((key b).comp_of_eq (continuous_swap.tendsto (⊤, b)) rfl).congr <|
          eventually_of_forall fun _ ↦ mul_comm ..
      | (a : ℕ), (b : ℕ) => by
        simp [ContinuousAt, nhds_prod_eq, tendsto_pure_nhds]

end ENat
