/-
Copyright (c) 2024 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.T5
import Mathlib.Data.Real.ENatENNReal

/-!
# Topology on extended natural numbers
-/

noncomputable section

open Set Filter Metric Function
open scoped Topology ENNReal NNReal ENat

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENat

variable {a b c d : ℕ∞} {r p q : ℕ} {x y z : ℕ∞} {s : Set ℕ∞}

-- TODO: Add in a suitable file.
lemma toNat_eq_toNat (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a.toNat = b.toNat ↔ a = b :=
  ⟨fun h ↦ by simpa [ha, hb] using WithTop.untop'_eq_untop'_iff.mp h, fun h ↦ congrArg toNat h⟩

-- TODO: Add in a suitable file.
lemma range_nat_cast : Set.range ((↑) : ℕ → ℕ∞) = Iio (⊤ : ℕ∞) := by
  ext n
  simp only [mem_Iio]
  exact ⟨fun ⟨m, hm⟩ ↦ hm.symm ▸ coe_lt_top m, fun h ↦ Option.ne_none_iff_exists.mp h.ne_top⟩

-- TODO: Add in a suitable file.
lemma Ico_eq_Iio (b : ℕ∞) : Ico 0 b = Iio b := by ext x; simp

-- TODO: Add in a suitable file.
lemma Icc_eq_Iic (b : ℕ∞) : Icc 0 b = Iic b := by ext x; simp

section TopologicalSpace

open TopologicalSpace

/-- Topology on `ℕ∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, while all neighborhoods of `∞` in `ℕ∞` contain infinite intervals. -/
instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

example : OrderClosedTopology ℕ∞ := by infer_instance

-- short-circuit type class inference
instance : T2Space ℕ∞ := inferInstance
instance : T5Space ℕ∞ := inferInstance
instance : T4Space ℕ∞ := inferInstance

example : StrictMono ((↑) : ℕ → ℕ∞) := by exact Nat.strictMono_cast

theorem embedding_coe : Embedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.embedding_of_ordConnected <| by rw [range_nat_cast]; exact ordConnected_Iio

theorem isOpen_ne_top : IsOpen {a : ℕ∞ | a ≠ ⊤} := isOpen_ne

theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by rw [ENat.Ico_eq_Iio]; exact isOpen_Iio

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨embedding_coe, by rw [range_nat_cast]; exact isOpen_Iio⟩

theorem coe_range_mem_nhds : range ((↑) : ℕ → ℕ∞) ∈ 𝓝 (r : ℕ∞) :=
  IsOpen.mem_nhds openEmbedding_coe.isOpen_range <| mem_range_self _

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : ℕ → ℕ∞) :=
  embedding_coe.continuous

theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℕ} :
    (Continuous fun a ↦ (f a : ℕ∞)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm

theorem nhds_coe {r : ℕ} : 𝓝 (r : ℕ∞) = (𝓝 r).map (↑) :=
  (openEmbedding_coe.map_nhds_eq r).symm

theorem tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : ℕ} {f : ℕ∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : ℕ → α) (𝓝 x) l := by
  rw [nhds_coe, tendsto_map'_iff]

theorem continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : ℕ} {f : ℕ∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : ℕ → α) x :=
  tendsto_nhds_coe_iff

theorem nhds_coe_coe {r p : ℕ} :
    𝓝 ((r : ℕ∞), (p : ℕ∞)) = (𝓝 (r, p)).map fun p : ℕ × ℕ => (↑p.1, ↑p.2) :=
  ((openEmbedding_coe.prod openEmbedding_coe).map_nhds_eq (r, p)).symm

theorem tendsto_toNat {a : ℕ∞} (ha : a ≠ ⊤) :
    Tendsto ENat.toNat (𝓝 a) (𝓝 a.toNat) := by
  lift a to ℕ using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

theorem eventuallyEq_of_toNat_eventuallyEq {l : Filter α} {f g : α → ℕ∞}
    (hfi : ∀ᶠ x in l, f x ≠ ⊤) (hgi : ∀ᶠ x in l, g x ≠ ⊤)
    (hfg : (fun x => (f x).toNat) =ᶠ[l] fun x => (g x).toNat) : f =ᶠ[l] g := by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENat.toNat_eq_toNat hfx hgx]

theorem continuousOn_toNat : ContinuousOn ENat.toNat {a | a ≠ ⊤} := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNat ha)

lemma continuousAt_toNat (hx : x ≠ ⊤) : ContinuousAt ENat.toNat x :=
  continuousOn_toNat.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

theorem nhds_top : 𝓝 (⊤ : ℕ∞) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]

theorem nhds_zero : 𝓝 (0 : ℕ∞) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [pos_iff_ne_zero, Iio]

theorem nhds_zero_basis : (𝓝 (0 : ℕ∞)).HasBasis (fun a : ℕ∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis

end TopologicalSpace

end ENat
