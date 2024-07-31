/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Monotone

/-!
# Topology on extended natural numbers
-/

open Set

open scoped Topology Filter

namespace ENat

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

@[simp] theorem range_coe' : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe

theorem embedding_coe : Embedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.embedding_of_ordConnected <| range_coe' ▸ ordConnected_Iio

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨embedding_coe, range_coe' ▸ isOpen_Iio⟩

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  lift x to ℕ using hx
  rw [← image_singleton, ← openEmbedding_coe.open_iff_image_open]
  trivial

theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  rw [_root_.mem_nhds_iff]
  exact ⟨fun ⟨_, h, _, h'⟩ ↦ h h', fun h ↦ ⟨_, singleton_subset_iff.2 h, isOpen_singleton hx, rfl⟩⟩

@[simp] theorem mem_nhds_coe_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (coe_ne_top _)

@[simp] theorem nhds_cast_eq (n : ℕ) : 𝓝 (n : ℕ∞) = 𝓟 ({(n : ℕ∞)}) := by
  ext; simp

@[simp] theorem nhds_cast_cast {m n : ℕ} :
    𝓝 ((m : ℕ∞), (n : ℕ∞)) = 𝓟 {((m : ℕ∞),(n : ℕ∞))} := by
  rw [((openEmbedding_coe.prod openEmbedding_coe).map_nhds_eq (m, n)).symm]
  simp

instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  simp only [ContinuousAt, WithTop.some_eq_coe, ENat.some_eq_coe]
  rw [nhds_cast_cast, ← Nat.cast_add, nhds_cast_eq]
  simp

end ENat
