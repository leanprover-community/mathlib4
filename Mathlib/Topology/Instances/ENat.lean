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

open Set

open scoped Topology Filter

namespace ENat

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

@[simp] theorem range_natCast : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe

theorem embedding_natCast : Embedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.embedding_of_ordConnected <| range_natCast ▸ ordConnected_Iio

theorem openEmbedding_natCast : OpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨embedding_natCast, range_natCast ▸ isOpen_Iio⟩

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  lift x to ℕ using hx
  rw [← image_singleton, ← openEmbedding_natCast.open_iff_image_open]
  trivial

theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  rw [_root_.mem_nhds_iff]
  exact ⟨fun ⟨_, h, _, h'⟩ ↦ h h', fun h ↦ ⟨_, singleton_subset_iff.2 h, isOpen_singleton hx, rfl⟩⟩

theorem mem_nhds_natCast_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (coe_ne_top _)

@[simp] theorem nhds_natCast (n : ℕ) : 𝓝 (n : ℕ∞) = 𝓟 ({(n : ℕ∞)}) := by
  ext; simp [mem_nhds_natCast_iff]

instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  simp only [ContinuousAt, WithTop.some_eq_coe, ENat.some_eq_coe]
  rw [nhds_prod_eq, nhds_natCast, nhds_natCast, ← Nat.cast_add, nhds_natCast]
  simp

end ENat
