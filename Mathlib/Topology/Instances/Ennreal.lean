/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module topology.instances.ennreal
! leanprover-community/mathlib commit 57ac39bd365c2f80589a700f9fbb664d3a1a30c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Instances.Nnreal
import Mathbin.Topology.Algebra.Order.MonotoneContinuity
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.Algebra.InfiniteSum.Real

/-!
# Extended non-negative reals
-/


noncomputable section

open Classical Set Filter Metric

open Classical Topology ENNReal NNReal BigOperators Filter

variable {α : Type _} {β : Type _} {γ : Type _}

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `emetric_space` topology. The `emetric_space` topology has
`is_open {⊤}`, while this topology doesn't have singleton elements. -/
instance : TopologicalSpace ℝ≥0∞ :=
  Preorder.topology ℝ≥0∞

instance : OrderTopology ℝ≥0∞ :=
  ⟨rfl⟩

instance : T2Space ℝ≥0∞ := by infer_instance

-- short-circuit type class inference
instance : NormalSpace ℝ≥0∞ :=
  normalOfCompactT2

instance : SecondCountableTopology ℝ≥0∞ :=
  orderIsoUnitIntervalBirational.toHomeomorph.Embedding.SecondCountableTopology

theorem embedding_coe : Embedding (coe : ℝ≥0 → ℝ≥0∞) :=
  ⟨⟨by
      refine' le_antisymm _ _
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0∞ _, ← coinduced_le_iff_le_induced]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        show IsOpen { b : ℝ≥0 | a < ↑b }
        · cases a <;> simp [none_eq_top, some_eq_coe, isOpen_lt']
        show IsOpen { b : ℝ≥0 | ↑b < a }
        · cases a <;> simp [none_eq_top, some_eq_coe, isOpen_gt', isOpen_const]
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0 _]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        exact ⟨Ioi a, isOpen_Ioi, by simp [Ioi]⟩
        exact ⟨Iio a, isOpen_Iio, by simp [Iio]⟩⟩, fun a b => coe_eq_coe.1⟩
#align ennreal.embedding_coe ENNReal.embedding_coe

theorem isOpen_ne_top : IsOpen { a : ℝ≥0∞ | a ≠ ⊤ } :=
  isOpen_ne
#align ennreal.is_open_ne_top ENNReal.isOpen_ne_top

theorem isOpen_Ico_zero : IsOpen (Ico 0 b) :=
  by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio
#align ennreal.is_open_Ico_zero ENNReal.isOpen_Ico_zero

theorem openEmbedding_coe : OpenEmbedding (coe : ℝ≥0 → ℝ≥0∞) :=
  ⟨embedding_coe, by
    convert is_open_ne_top
    ext (x | _) <;> simp [none_eq_top, some_eq_coe]⟩
#align ennreal.open_embedding_coe ENNReal.openEmbedding_coe

theorem coe_range_mem_nhds : range (coe : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds openEmbedding_coe.open_range <| mem_range_self _
#align ennreal.coe_range_mem_nhds ENNReal.coe_range_mem_nhds

@[norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {a : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ≥0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm
#align ennreal.tendsto_coe ENNReal.tendsto_coe

theorem continuous_coe : Continuous (coe : ℝ≥0 → ℝ≥0∞) :=
  embedding_coe.Continuous
#align ennreal.continuous_coe ENNReal.continuous_coe

theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℝ≥0} :
    (Continuous fun a => (f a : ℝ≥0∞)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm
#align ennreal.continuous_coe_iff ENNReal.continuous_coe_iff

theorem nhds_coe {r : ℝ≥0} : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map coe :=
  (openEmbedding_coe.map_nhds_eq r).symm
#align ennreal.nhds_coe ENNReal.nhds_coe

theorem tendsto_nhds_coe_iff {α : Type _} {l : Filter α} {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ coe : ℝ≥0 → α) (𝓝 x) l :=
  show _ ≤ _ ↔ _ ≤ _ by rw [nhds_coe, Filter.map_map]
#align ennreal.tendsto_nhds_coe_iff ENNReal.tendsto_nhds_coe_iff

theorem continuousAt_coe_iff {α : Type _} [TopologicalSpace α] {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ coe : ℝ≥0 → α) x :=
  tendsto_nhds_coe_iff
#align ennreal.continuous_at_coe_iff ENNReal.continuousAt_coe_iff

theorem nhds_coe_coe {r p : ℝ≥0} :
    𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map fun p : ℝ≥0 × ℝ≥0 => (p.1, p.2) :=
  ((openEmbedding_coe.Prod openEmbedding_coe).map_nhds_eq (r, p)).symm
#align ennreal.nhds_coe_coe ENNReal.nhds_coe_coe

theorem continuous_ofReal : Continuous ENNReal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal
#align ennreal.continuous_of_real ENNReal.continuous_ofReal

theorem tendsto_ofReal {f : Filter α} {m : α → ℝ} {a : ℝ} (h : Tendsto m f (𝓝 a)) :
    Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a)) :=
  Tendsto.comp (Continuous.tendsto continuous_ofReal _) h
#align ennreal.tendsto_of_real ENNReal.tendsto_ofReal

theorem tendsto_toNNReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal) :=
  by
  lift a to ℝ≥0 using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
#align ennreal.tendsto_to_nnreal ENNReal.tendsto_toNNReal

theorem eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α → ℝ≥0∞}
    (hfi : ∀ᶠ x in l, f x ≠ ∞) (hgi : ∀ᶠ x in l, g x ≠ ∞)
    (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g :=
  by
  filter_upwards [hfi, hgi, hfg]with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal hfx hgx]
#align ennreal.eventually_eq_of_to_real_eventually_eq ENNReal.eventuallyEq_of_toReal_eventuallyEq

theorem continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a ≠ ∞ } := fun a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)
#align ennreal.continuous_on_to_nnreal ENNReal.continuousOn_toNNReal

theorem tendsto_toReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  NNReal.tendsto_coe.2 <| tendsto_toNNReal ha
#align ennreal.tendsto_to_real ENNReal.tendsto_toReal

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def neTopHomeomorphNnreal : { a | a ≠ ∞ } ≃ₜ ℝ≥0 :=
  {
    neTopEquivNNReal with
    continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toNNReal
    continuous_invFun := continuous_coe.subtype_mk _ }
#align ennreal.ne_top_homeomorph_nnreal ENNReal.neTopHomeomorphNnreal

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def ltTopHomeomorphNnreal : { a | a < ∞ } ≃ₜ ℝ≥0 := by
  refine' (Homeomorph.setCongr <| Set.ext fun x => _).trans ne_top_homeomorph_nnreal <;>
    simp only [mem_set_of_eq, lt_top_iff_ne_top]
#align ennreal.lt_top_homeomorph_nnreal ENNReal.ltTopHomeomorphNnreal

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » ennreal.top()) -/
theorem nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a ≠ ∞), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]
#align ennreal.nhds_top ENNReal.nhds_top

theorem nhds_top' : 𝓝 ∞ = ⨅ r : ℝ≥0, 𝓟 (Ioi r) :=
  nhds_top.trans <| infᵢ_ne_top _
#align ennreal.nhds_top' ENNReal.nhds_top'

theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  nhds_top_basis
#align ennreal.nhds_top_basis ENNReal.nhds_top_basis

theorem tendsto_nhds_top_iff_nNReal {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ≥0, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_infi, tendsto_principal, mem_Ioi]
#align ennreal.tendsto_nhds_top_iff_nnreal ENNReal.tendsto_nhds_top_iff_nNReal

theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a :=
  tendsto_nhds_top_iff_nNReal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_nat] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
      (h n).mono fun y => lt_trans <| by rwa [← ENNReal.coe_nat, coe_lt_coe]⟩
#align ennreal.tendsto_nhds_top_iff_nat ENNReal.tendsto_nhds_top_iff_nat

theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) :
    Tendsto m f (𝓝 ⊤) :=
  tendsto_nhds_top_iff_nat.2 h
#align ennreal.tendsto_nhds_top ENNReal.tendsto_nhds_top

theorem tendsto_nat_nhds_top : Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞) :=
  tendsto_nhds_top fun n =>
    mem_atTop_sets.2 ⟨n + 1, fun m hm => mem_setOf.2 <| Nat.cast_lt.2 <| Nat.lt_of_succ_le hm⟩
#align ennreal.tendsto_nat_nhds_top ENNReal.tendsto_nat_nhds_top

@[simp, norm_cast]
theorem tendsto_coe_nhds_top {f : α → ℝ≥0} {l : Filter α} :
    Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_nnreal, at_top_basis_Ioi.tendsto_right_iff] <;> [simp, infer_instance,
    infer_instance]
#align ennreal.tendsto_coe_nhds_top ENNReal.tendsto_coe_nhds_top

theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞) :=
  tendsto_coe_nhds_top.2 tendsto_real_toNNReal_atTop
#align ennreal.tendsto_of_real_at_top ENNReal.tendsto_ofReal_atTop

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » 0) -/
theorem nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [bot_lt_iff_ne_bot, Iio]
#align ennreal.nhds_zero ENNReal.nhds_zero

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis
#align ennreal.nhds_zero_basis ENNReal.nhds_zero_basis

theorem nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic
#align ennreal.nhds_zero_basis_Iic ENNReal.nhds_zero_basis_Iic

@[instance]
theorem nhdsWithin_Ioi_coe_neBot {r : ℝ≥0} : (𝓝[>] (r : ℝ≥0∞)).ne_bot :=
  nhdsWithin_Ioi_self_neBot' ⟨⊤, ENNReal.coe_lt_top⟩
#align ennreal.nhds_within_Ioi_coe_ne_bot ENNReal.nhdsWithin_Ioi_coe_neBot

@[instance]
theorem nhdsWithin_Ioi_zero_neBot : (𝓝[>] (0 : ℝ≥0∞)).ne_bot :=
  nhdsWithin_Ioi_coe_neBot
#align ennreal.nhds_within_Ioi_zero_ne_bot ENNReal.nhdsWithin_Ioi_zero_neBot

-- using Icc because
-- • don't have 'Ioo (x - ε) (x + ε) ∈ 𝓝 x' unless x > 0
-- • (x - y ≤ ε ↔ x ≤ ε + y) is true, while (x - y < ε ↔ x < ε + y) is not
theorem Icc_mem_nhds (xt : x ≠ ⊤) (ε0 : ε ≠ 0) : Icc (x - ε) (x + ε) ∈ 𝓝 x :=
  by
  rw [_root_.mem_nhds_iff]
  by_cases x0 : x = 0
  · use Iio (x + ε)
    have : Iio (x + ε) ⊆ Icc (x - ε) (x + ε)
    intro a
    rw [x0]
    simpa using le_of_lt
    use this
    exact ⟨isOpen_Iio, mem_Iio_self_add xt ε0⟩
  · use Ioo (x - ε) (x + ε)
    use Ioo_subset_Icc_self
    exact ⟨isOpen_Ioo, mem_Ioo_self_sub_add xt x0 ε0 ε0⟩
#align ennreal.Icc_mem_nhds ENNReal.Icc_mem_nhds

theorem nhds_of_ne_top (xt : x ≠ ⊤) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
  by
  refine' le_antisymm _ _
  -- first direction
  simp only [le_infᵢ_iff, le_principal_iff];
  intro ε ε0; exact Icc_mem_nhds xt ε0.lt.ne'
  -- second direction
  rw [nhds_generate_from];
  refine' le_infᵢ fun s => le_infᵢ fun hs => _
  rcases hs with ⟨xs, ⟨a, (rfl : s = Ioi a) | (rfl : s = Iio a)⟩⟩
  · rcases exists_between xs with ⟨b, ab, bx⟩
    have xb_pos : 0 < x - b := tsub_pos_iff_lt.2 bx
    have xxb : x - (x - b) = b := sub_sub_cancel xt bx.le
    refine' infᵢ_le_of_le (x - b) (infᵢ_le_of_le xb_pos _)
    simp only [mem_principal, le_principal_iff]
    intro y
    rintro ⟨h₁, h₂⟩
    rw [xxb] at h₁
    calc
      a < b := ab
      _ ≤ y := h₁
      
  · rcases exists_between xs with ⟨b, xb, ba⟩
    have bx_pos : 0 < b - x := tsub_pos_iff_lt.2 xb
    have xbx : x + (b - x) = b := add_tsub_cancel_of_le xb.le
    refine' infᵢ_le_of_le (b - x) (infᵢ_le_of_le bx_pos _)
    simp only [mem_principal, le_principal_iff]
    intro y
    rintro ⟨h₁, h₂⟩
    rw [xbx] at h₂
    calc
      y ≤ b := h₂
      _ < a := ba
      
#align ennreal.nhds_of_ne_top ENNReal.nhds_of_ne_top

/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (a - ε) (a + ε) := by
  simp only [nhds_of_ne_top ha, tendsto_infi, tendsto_principal, mem_Icc]
#align ennreal.tendsto_nhds ENNReal.tendsto_nhds

protected theorem tendsto_nhds_zero {f : Filter α} {u : α → ℝ≥0∞} :
    Tendsto u f (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ≤ ε :=
  by
  rw [ENNReal.tendsto_nhds zero_ne_top]
  simp only [true_and_iff, zero_tsub, zero_le, zero_add, Set.mem_Icc]
#align ennreal.tendsto_nhds_zero ENNReal.tendsto_nhds_zero

protected theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : a ≠ ⊤) : Tendsto f atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Icc (a - ε) (a + ε) := by
  simp only [ENNReal.tendsto_nhds ha, mem_at_top_sets, mem_set_of_eq, Filter.Eventually]
#align ennreal.tendsto_at_top ENNReal.tendsto_atTop

instance : ContinuousAdd ℝ≥0∞ :=
  by
  refine' ⟨continuous_iff_continuousAt.2 _⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (· ∘ ·),
    tendsto_coe, tendsto_add]

protected theorem tendsto_atTop_zero [hβ : Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} :
    Filter.atTop.Tendsto f (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε :=
  by
  rw [ENNReal.tendsto_atTop zero_ne_top]
  · simp_rw [Set.mem_Icc, zero_add, zero_tsub, zero_le _, true_and_iff]
  · exact hβ
#align ennreal.tendsto_at_top_zero ENNReal.tendsto_atTop_zero

theorem tendsto_sub {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b)) :=
  by
  cases a <;> cases b
  · simp only [eq_self_iff_true, not_true, Ne.def, none_eq_top, or_self_iff] at h
    contradiction
  · simp only [some_eq_coe, WithTop.top_sub_coe, none_eq_top]
    apply tendsto_nhds_top_iff_nnreal.2 fun n => _
    rw [nhds_prod_eq, eventually_prod_iff]
    refine'
      ⟨fun z => (n + (b + 1) : ℝ≥0∞) < z,
        Ioi_mem_nhds (by simp only [one_lt_top, add_lt_top, coe_lt_top, and_self_iff]), fun z =>
        z < b + 1, Iio_mem_nhds (ENNReal.lt_add_right coe_ne_top one_ne_zero), fun x hx y hy => _⟩
    dsimp
    rw [lt_tsub_iff_right]
    have : (n : ℝ≥0∞) + y + (b + 1) < x + (b + 1) :=
      calc
        (n : ℝ≥0∞) + y + (b + 1) = (n : ℝ≥0∞) + (b + 1) + y := by abel
        _ < x + (b + 1) := ENNReal.add_lt_add hx hy
        
    exact lt_of_add_lt_add_right this
  · simp only [some_eq_coe, WithTop.sub_top, none_eq_top]
    suffices H : ∀ᶠ p : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (a, ∞), 0 = p.1 - p.2
    exact tendsto_const_nhds.congr' H
    rw [nhds_prod_eq, eventually_prod_iff]
    refine'
      ⟨fun z => z < a + 1, Iio_mem_nhds (ENNReal.lt_add_right coe_ne_top one_ne_zero), fun z =>
        (a : ℝ≥0∞) + 1 < z,
        Ioi_mem_nhds (by simp only [one_lt_top, add_lt_top, coe_lt_top, and_self_iff]),
        fun x hx y hy => _⟩
    rw [eq_comm]
    simp only [tsub_eq_zero_iff_le, (LT.lt.trans hx hy).le]
  · simp only [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, Function.comp, ← ENNReal.coe_sub,
      tendsto_coe]
    exact Continuous.tendsto (by continuity) _
#align ennreal.tendsto_sub ENNReal.tendsto_sub

protected theorem Tendsto.sub {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun a => ma a - mb a) f (𝓝 (a - b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prod_mk_nhds hmb)
#align ennreal.tendsto.sub ENNReal.Tendsto.sub

protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
  by
  have ht :
    ∀ b : ℝ≥0∞, b ≠ 0 → Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 ((⊤ : ℝ≥0∞), b)) (𝓝 ⊤) :=
    by
    refine' fun b hb => tendsto_nhds_top_iff_nnreal.2 fun n => _
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : ∀ᶠ c : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (∞, b), ↑n / ↑ε < c.1 ∧ ↑ε < c.2 :=
      (lt_mem_nhds <| div_lt_top coe_ne_top hε.ne').prod_nhds (lt_mem_nhds hεb)
    refine' this.mono fun c hc => _
    exact (ENNReal.div_mul_cancel hε.ne' coe_ne_top).symm.trans_lt (mul_lt_mul hc.1 hc.2)
  cases a
  · simp [none_eq_top] at hb
    simp [none_eq_top, ht b hb, top_mul, hb]
  cases b
  · simp [none_eq_top] at ha
    simp [*, nhds_swap (a : ℝ≥0∞) ⊤, none_eq_top, some_eq_coe, top_mul, tendsto_map'_iff, (· ∘ ·),
      mul_comm]
  simp [some_eq_coe, nhds_coe_coe, tendsto_map'_iff, (· ∘ ·)]
  simp only [coe_mul.symm, tendsto_coe, tendsto_mul]
#align ennreal.tendsto_mul ENNReal.tendsto_mul

protected theorem Tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ 0 ∨ a ≠ ⊤) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prod_mk_nhds hmb)
#align ennreal.tendsto.mul ENNReal.Tendsto.mul

theorem ContinuousOn.eNNReal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : ∀ x ∈ s, f x ≠ 0 ∨ g x ≠ ∞)
    (h₂ : ∀ x ∈ s, g x ≠ 0 ∨ f x ≠ ∞) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)
#align continuous_on.ennreal_mul ContinuousOn.eNNReal_mul

theorem Continuous.eNNReal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : ∀ x, f x ≠ 0 ∨ g x ≠ ∞) (h₂ : ∀ x, g x ≠ 0 ∨ f x ≠ ∞) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.ContinuousAt (h₁ x) hg.ContinuousAt (h₂ x)
#align continuous.ennreal_mul Continuous.eNNReal_mul

protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun this : a = 0 => by simp [this, tendsto_const_nhds]) fun ha : a ≠ 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb
#align ennreal.tendsto.const_mul ENNReal.Tendsto.const_mul

protected theorem Tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) : Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha
#align ennreal.tendsto.mul_const ENNReal.Tendsto.mul_const

theorem tendsto_finset_prod_of_ne_top {ι : Type _} {f : ι → α → ℝ≥0∞} {x : Filter α} {a : ι → ℝ≥0∞}
    (s : Finset ι) (h : ∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) (h' : ∀ i ∈ s, a i ≠ ∞) :
    Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
  by
  induction' s using Finset.induction with a s has IH; · simp [tendsto_const_nhds]
  simp only [Finset.prod_insert has]
  apply tendsto.mul (h _ (Finset.mem_insert_self _ _))
  · right
    exact (prod_lt_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)).Ne
  ·
    exact
      IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi =>
        h' _ (Finset.mem_insert_of_mem hi)
  · exact Or.inr (h' _ (Finset.mem_insert_self _ _))
#align ennreal.tendsto_finset_prod_of_ne_top ENNReal.tendsto_finset_prod_of_ne_top

protected theorem continuousAt_const_mul {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) :
    ContinuousAt ((· * ·) a) b :=
  Tendsto.const_mul tendsto_id h.symm
#align ennreal.continuous_at_const_mul ENNReal.continuousAt_const_mul

protected theorem continuousAt_mul_const {a b : ℝ≥0∞} (h : a ≠ ⊤ ∨ b ≠ 0) :
    ContinuousAt (fun x => x * a) b :=
  Tendsto.mul_const tendsto_id h.symm
#align ennreal.continuous_at_mul_const ENNReal.continuousAt_mul_const

protected theorem continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ⊤) : Continuous ((· * ·) a) :=
  continuous_iff_continuousAt.2 fun x => ENNReal.continuousAt_const_mul (Or.inl ha)
#align ennreal.continuous_const_mul ENNReal.continuous_const_mul

protected theorem continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ⊤) : Continuous fun x => x * a :=
  continuous_iff_continuousAt.2 fun x => ENNReal.continuousAt_mul_const (Or.inl ha)
#align ennreal.continuous_mul_const ENNReal.continuous_mul_const

protected theorem continuous_div_const (c : ℝ≥0∞) (c_ne_zero : c ≠ 0) :
    Continuous fun x : ℝ≥0∞ => x / c :=
  by
  simp_rw [div_eq_mul_inv, continuous_iff_continuousAt]
  intro x
  exact ENNReal.continuousAt_mul_const (Or.intro_left _ (inv_ne_top.mpr c_ne_zero))
#align ennreal.continuous_div_const ENNReal.continuous_div_const

@[continuity]
theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n :=
  by
  induction' n with n IH
  · simp [continuous_const]
  simp_rw [Nat.succ_eq_add_one, pow_add, pow_one, continuous_iff_continuousAt]
  intro x
  refine' ENNReal.Tendsto.mul (IH.tendsto _) _ tendsto_id _ <;> by_cases H : x = 0
  · simp only [H, zero_ne_top, Ne.def, or_true_iff, not_false_iff]
  · exact Or.inl fun h => H (pow_eq_zero h)
  ·
    simp only [H, pow_eq_top_iff, zero_ne_top, false_or_iff, eq_self_iff_true, not_true, Ne.def,
      not_false_iff, false_and_iff]
  · simp only [H, true_or_iff, Ne.def, not_false_iff]
#align ennreal.continuous_pow ENNReal.continuous_pow

theorem continuousOn_sub :
    ContinuousOn (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) { p : ℝ≥0∞ × ℝ≥0∞ | p ≠ ⟨∞, ∞⟩ } :=
  by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne.def, Set.mem_setOf_eq, Prod.mk.inj_iff] at hp
  refine' tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_distrib.mp hp))
#align ennreal.continuous_on_sub ENNReal.continuousOn_sub

theorem continuous_sub_left {a : ℝ≥0∞} (a_ne_top : a ≠ ⊤) : Continuous fun x => a - x :=
  by
  rw [show (fun x => a - x) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨a, x⟩ by rfl]
  apply ContinuousOn.comp_continuous continuous_on_sub (Continuous.Prod.mk a)
  intro x
  simp only [a_ne_top, Ne.def, mem_set_of_eq, Prod.mk.inj_iff, false_and_iff, not_false_iff]
#align ennreal.continuous_sub_left ENNReal.continuous_sub_left

theorem continuous_nNReal_sub {a : ℝ≥0} : Continuous fun x : ℝ≥0∞ => (a : ℝ≥0∞) - x :=
  continuous_sub_left coe_ne_top
#align ennreal.continuous_nnreal_sub ENNReal.continuous_nNReal_sub

theorem continuousOn_sub_left (a : ℝ≥0∞) : ContinuousOn (fun x => a - x) { x : ℝ≥0∞ | x ≠ ∞ } :=
  by
  rw [show (fun x => a - x) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨a, x⟩ by rfl]
  apply ContinuousOn.comp continuous_on_sub (Continuous.continuousOn (Continuous.Prod.mk a))
  rintro _ h (_ | _)
  exact h none_eq_top
#align ennreal.continuous_on_sub_left ENNReal.continuousOn_sub_left

theorem continuous_sub_right (a : ℝ≥0∞) : Continuous fun x : ℝ≥0∞ => x - a :=
  by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const]
  · rw [show (fun x => x - a) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply ContinuousOn.comp_continuous continuous_on_sub (continuous_id'.prod_mk continuous_const)
    intro x
    simp only [a_infty, Ne.def, mem_set_of_eq, Prod.mk.inj_iff, and_false_iff, not_false_iff]
#align ennreal.continuous_sub_right ENNReal.continuous_sub_right

protected theorem Tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((continuous_pow n).Tendsto a).comp hm
#align ennreal.tendsto.pow ENNReal.Tendsto.pow

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0∞} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  by
  have : tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  haveI : (𝓝[<] (1 : ℝ≥0∞)).ne_bot := nhdsWithin_Iio_self_neBot' ⟨0, zero_lt_one⟩
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| eventually_of_forall h)
#align ennreal.le_of_forall_lt_one_mul_le ENNReal.le_of_forall_lt_one_mul_le

theorem infᵢ_mul_left' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0)
    (h0 : a = 0 → Nonempty ι) : (⨅ i, a * f i) = a * ⨅ i, f i :=
  by
  by_cases H : a = ⊤ ∧ (⨅ i, f i) = 0
  · rcases h H.1 H.2 with ⟨i, hi⟩
    rw [H.2, mul_zero, ← bot_eq_zero, infᵢ_eq_bot]
    exact fun b hb => ⟨i, by rwa [hi, mul_zero, ← bot_eq_zero]⟩
  · rw [not_and_or] at H
    cases isEmpty_or_nonempty ι
    · rw [infᵢ_of_empty, infᵢ_of_empty, mul_top, if_neg]
      exact mt h0 (not_nonempty_iff.2 ‹_›)
    ·
      exact
        (ennreal.mul_left_mono.map_infi_of_continuous_at' (ENNReal.continuousAt_const_mul H)).symm
#align ennreal.infi_mul_left' ENNReal.infᵢ_mul_left'

theorem infᵢ_mul_left {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
    (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) : (⨅ i, a * f i) = a * ⨅ i, f i :=
  infᵢ_mul_left' h fun _ => ‹Nonempty ι›
#align ennreal.infi_mul_left ENNReal.infᵢ_mul_left

theorem infᵢ_mul_right' {ι} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0)
    (h0 : a = 0 → Nonempty ι) : (⨅ i, f i * a) = (⨅ i, f i) * a := by
  simpa only [mul_comm a] using infi_mul_left' h h0
#align ennreal.infi_mul_right' ENNReal.infᵢ_mul_right'

theorem infᵢ_mul_right {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {a : ℝ≥0∞}
    (h : a = ⊤ → (⨅ i, f i) = 0 → ∃ i, f i = 0) : (⨅ i, f i * a) = (⨅ i, f i) * a :=
  infᵢ_mul_right' h fun _ => ‹Nonempty ι›
#align ennreal.infi_mul_right ENNReal.infᵢ_mul_right

theorem inv_map_infᵢ {ι : Sort _} {x : ι → ℝ≥0∞} : (infᵢ x)⁻¹ = ⨆ i, (x i)⁻¹ :=
  OrderIso.invENNReal.map_infᵢ x
#align ennreal.inv_map_infi ENNReal.inv_map_infᵢ

theorem inv_map_supᵢ {ι : Sort _} {x : ι → ℝ≥0∞} : (supᵢ x)⁻¹ = ⨅ i, (x i)⁻¹ :=
  OrderIso.invENNReal.map_supᵢ x
#align ennreal.inv_map_supr ENNReal.inv_map_supᵢ

theorem inv_limsup {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l := by
  simp only [limsup_eq_infi_supr, inv_map_infi, inv_map_supr, liminf_eq_supr_infi]
#align ennreal.inv_limsup ENNReal.inv_limsup

theorem inv_liminf {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l := by
  simp only [limsup_eq_infi_supr, inv_map_infi, inv_map_supr, liminf_eq_supr_infi]
#align ennreal.inv_liminf ENNReal.inv_liminf

instance : ContinuousInv ℝ≥0∞ :=
  ⟨OrderIso.invENNReal.Continuous⟩

@[simp]
protected theorem tendsto_inv_iff {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun x => (m x)⁻¹) f (𝓝 a⁻¹) ↔ Tendsto m f (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using tendsto.inv h, Tendsto.inv⟩
#align ennreal.tendsto_inv_iff ENNReal.tendsto_inv_iff

protected theorem Tendsto.div {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ ⊤ ∨ a ≠ ⊤) : Tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) := by
  apply tendsto.mul hma _ (ENNReal.tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]
#align ennreal.tendsto.div ENNReal.Tendsto.div

protected theorem Tendsto.const_div {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ ⊤ ∨ a ≠ ⊤) : Tendsto (fun b => a / m b) f (𝓝 (a / b)) :=
  by
  apply tendsto.const_mul (ENNReal.tendsto_inv_iff.2 hm)
  simp [hb]
#align ennreal.tendsto.const_div ENNReal.Tendsto.const_div

protected theorem Tendsto.div_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => m x / b) f (𝓝 (a / b)) :=
  by
  apply tendsto.mul_const hm
  simp [ha]
#align ennreal.tendsto.div_const ENNReal.Tendsto.div_const

protected theorem tendsto_inv_nat_nhds_zero : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
  ENNReal.inv_top ▸ ENNReal.tendsto_inv_iff.2 tendsto_nat_nhds_top
#align ennreal.tendsto_inv_nat_nhds_zero ENNReal.tendsto_inv_nat_nhds_zero

theorem supᵢ_add {ι : Sort _} {s : ι → ℝ≥0∞} [h : Nonempty ι] : supᵢ s + a = ⨆ b, s b + a :=
  Monotone.map_supᵢ_of_continuousAt' (continuousAt_id.add continuousAt_const) <|
    monotone_id.add monotone_const
#align ennreal.supr_add ENNReal.supᵢ_add

theorem bsupr_add' {ι : Sort _} {p : ι → Prop} (h : ∃ i, p i) {f : ι → ℝ≥0∞} :
    (⨆ (i) (hi : p i), f i) + a = ⨆ (i) (hi : p i), f i + a :=
  by
  haveI : Nonempty { i // p i } := nonempty_subtype.2 h
  simp only [supᵢ_subtype', supr_add]
#align ennreal.bsupr_add' ENNReal.bsupr_add'

theorem add_bsupr' {ι : Sort _} {p : ι → Prop} (h : ∃ i, p i) {f : ι → ℝ≥0∞} :
    (a + ⨆ (i) (hi : p i), f i) = ⨆ (i) (hi : p i), a + f i := by
  simp only [add_comm a, bsupr_add' h]
#align ennreal.add_bsupr' ENNReal.add_bsupr'

theorem bsupr_add {ι} {s : Set ι} (hs : s.Nonempty) {f : ι → ℝ≥0∞} :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a :=
  bsupr_add' hs
#align ennreal.bsupr_add ENNReal.bsupr_add

theorem add_bsupr {ι} {s : Set ι} (hs : s.Nonempty) {f : ι → ℝ≥0∞} :
    (a + ⨆ i ∈ s, f i) = ⨆ i ∈ s, a + f i :=
  add_bsupr' hs
#align ennreal.add_bsupr ENNReal.add_bsupr

theorem supₛ_add {s : Set ℝ≥0∞} (hs : s.Nonempty) : supₛ s + a = ⨆ b ∈ s, b + a := by
  rw [supₛ_eq_supᵢ, bsupr_add hs]
#align ennreal.Sup_add ENNReal.supₛ_add

theorem add_supᵢ {ι : Sort _} {s : ι → ℝ≥0∞} [Nonempty ι] : a + supᵢ s = ⨆ b, a + s b := by
  rw [add_comm, supr_add] <;> simp [add_comm]
#align ennreal.add_supr ENNReal.add_supᵢ

theorem supᵢ_add_supᵢ_le {ι ι' : Sort _} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0∞} {g : ι' → ℝ≥0∞}
    {a : ℝ≥0∞} (h : ∀ i j, f i + g j ≤ a) : supᵢ f + supᵢ g ≤ a := by
  simpa only [add_supr, supr_add] using supᵢ₂_le h
#align ennreal.supr_add_supr_le ENNReal.supᵢ_add_supᵢ_le

theorem bsupr_add_bsupr_le' {ι ι'} {p : ι → Prop} {q : ι' → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ℝ≥0∞} {g : ι' → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ (i) (hi : p i) (j) (hj : q j), f i + g j ≤ a) :
    ((⨆ (i) (hi : p i), f i) + ⨆ (j) (hj : q j), g j) ≤ a :=
  by
  simp_rw [bsupr_add' hp, add_bsupr' hq]
  exact supᵢ₂_le fun i hi => supᵢ₂_le (h i hi)
#align ennreal.bsupr_add_bsupr_le' ENNReal.bsupr_add_bsupr_le'

theorem bsupr_add_bsupr_le {ι ι'} {s : Set ι} {t : Set ι'} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℝ≥0∞} {g : ι' → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    ((⨆ i ∈ s, f i) + ⨆ j ∈ t, g j) ≤ a :=
  bsupr_add_bsupr_le' hs ht h
#align ennreal.bsupr_add_bsupr_le ENNReal.bsupr_add_bsupr_le

theorem supᵢ_add_supᵢ {ι : Sort _} {f g : ι → ℝ≥0∞} (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) :
    supᵢ f + supᵢ g = ⨆ a, f a + g a :=
  by
  cases isEmpty_or_nonempty ι
  · simp only [supᵢ_of_empty, bot_eq_zero, zero_add]
  · refine' le_antisymm _ (supᵢ_le fun a => add_le_add (le_supᵢ _ _) (le_supᵢ _ _))
    refine' supr_add_supr_le fun i j => _
    rcases h i j with ⟨k, hk⟩
    exact le_supᵢ_of_le k hk
#align ennreal.supr_add_supr ENNReal.supᵢ_add_supᵢ

theorem supᵢ_add_supᵢ_of_monotone {ι : Sort _} [SemilatticeSup ι] {f g : ι → ℝ≥0∞} (hf : Monotone f)
    (hg : Monotone g) : supᵢ f + supᵢ g = ⨆ a, f a + g a :=
  supᵢ_add_supᵢ fun i j => ⟨i ⊔ j, add_le_add (hf <| le_sup_left) (hg <| le_sup_right)⟩
#align ennreal.supr_add_supr_of_monotone ENNReal.supᵢ_add_supᵢ_of_monotone

theorem finset_sum_supᵢ_nat {α} {ι} [SemilatticeSup ι] {s : Finset α} {f : α → ι → ℝ≥0∞}
    (hf : ∀ a, Monotone (f a)) : (∑ a in s, supᵢ (f a)) = ⨆ n, ∑ a in s, f a n :=
  by
  refine' Finset.induction_on s _ _
  · simp
  · intro a s has ih
    simp only [Finset.sum_insert has]
    rw [ih, supr_add_supr_of_monotone (hf a)]
    intro i j h
    exact Finset.sum_le_sum fun a ha => hf a h
#align ennreal.finset_sum_supr_nat ENNReal.finset_sum_supᵢ_nat

theorem mul_supᵢ {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : a * supᵢ f = ⨆ i, a * f i :=
  by
  by_cases hf : ∀ i, f i = 0
  · obtain rfl : f = fun _ => 0
    exact funext hf
    simp only [supr_zero_eq_zero, mul_zero]
  · refine' (monotone_id.const_mul' _).map_supᵢ_of_continuousAt _ (mul_zero a)
    refine' ENNReal.Tendsto.const_mul tendsto_id (Or.inl _)
    exact mt supr_eq_zero.1 hf
#align ennreal.mul_supr ENNReal.mul_supᵢ

theorem mul_supₛ {s : Set ℝ≥0∞} {a : ℝ≥0∞} : a * supₛ s = ⨆ i ∈ s, a * i := by
  simp only [supₛ_eq_supᵢ, mul_supr]
#align ennreal.mul_Sup ENNReal.mul_supₛ

theorem supᵢ_mul {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : supᵢ f * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_supr] <;> congr <;> funext <;> rw [mul_comm]
#align ennreal.supr_mul ENNReal.supᵢ_mul

theorem supᵢ_div {ι : Sort _} {f : ι → ℝ≥0∞} {a : ℝ≥0∞} : supᵢ f / a = ⨆ i, f i / a :=
  supᵢ_mul
#align ennreal.supr_div ENNReal.supᵢ_div

protected theorem tendsto_coe_sub :
    ∀ {b : ℝ≥0∞}, Tendsto (fun b : ℝ≥0∞ => ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
  by
  refine' forall_ennreal.2 ⟨fun a => _, _⟩
  · simp [@nhds_coe a, tendsto_map'_iff, (· ∘ ·), tendsto_coe, ← WithTop.coe_sub]
    exact tendsto_const_nhds.sub tendsto_id
  simp
  exact
    (tendsto.congr'
        (mem_of_superset (lt_mem_nhds <| @coe_lt_top r) <| by
          simp (config := { contextual := true }) [le_of_lt]))
      tendsto_const_nhds
#align ennreal.tendsto_coe_sub ENNReal.tendsto_coe_sub

theorem sub_supᵢ {ι : Sort _} [Nonempty ι] {b : ι → ℝ≥0∞} (hr : a < ⊤) :
    (a - ⨆ i, b i) = ⨅ i, a - b i :=
  by
  let ⟨r, Eq, _⟩ := lt_iff_exists_coe.mp hr
  have : infₛ ((fun b => ↑r - b) '' range b) = ↑r - ⨆ i, b i :=
    IsGLB.infₛ_eq <|
      isLUB_supᵢ.isGLB_of_tendsto (fun x _ y _ => tsub_le_tsub (le_refl (r : ℝ≥0∞)))
        (range_nonempty _) (ENNReal.tendsto_coe_sub.comp (tendsto_id'.2 inf_le_left))
  rw [Eq, ← this] <;> simp [infₛ_image, infᵢ_range, -mem_range] <;> exact le_rfl
#align ennreal.sub_supr ENNReal.sub_supᵢ

theorem exists_countable_dense_no_zero_top :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s :=
  by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s :=
    exists_countable_dense_no_bot_top ℝ≥0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩
#align ennreal.exists_countable_dense_no_zero_top ENNReal.exists_countable_dense_no_zero_top

theorem exists_lt_add_of_lt_add {x y z : ℝ≥0∞} (h : x < y + z) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ y' z', y' < y ∧ z' < z ∧ x < y' + z' :=
  by
  haveI : ne_bot (𝓝[<] y) := nhdsWithin_Iio_self_neBot' ⟨0, pos_iff_ne_zero.2 hy⟩
  haveI : ne_bot (𝓝[<] z) := nhdsWithin_Iio_self_neBot' ⟨0, pos_iff_ne_zero.2 hz⟩
  have A : tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 + p.2) ((𝓝[<] y).Prod (𝓝[<] z)) (𝓝 (y + z)) :=
    by
    apply tendsto.mono_left _ (Filter.prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
    rw [← nhds_prod_eq]
    exact tendsto_add
  rcases(((tendsto_order.1 A).1 x h).And
        (Filter.prod_mem_prod self_mem_nhdsWithin self_mem_nhdsWithin)).exists with
    ⟨⟨y', z'⟩, hx, hy', hz'⟩
  exact ⟨y', z', hy', hz', hx⟩
#align ennreal.exists_lt_add_of_lt_add ENNReal.exists_lt_add_of_lt_add

end TopologicalSpace

section Liminf

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem exists_frequently_lt_of_liminf_ne_top {ι : Type _} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (‖x n‖₊ : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, x n < R :=
  by
  by_contra h
  simp_rw [not_exists, not_frequently, not_lt] at h
  refine'
    hx
      (ENNReal.eq_top_of_forall_nnreal_le fun r =>
        le_Liminf_of_le
          (by
            run_tac
              is_bounded_default)
          _)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r]with i hi using hi.trans ((coe_nnnorm (x i)).symm ▸ le_abs_self (x i))
#align ennreal.exists_frequently_lt_of_liminf_ne_top ENNReal.exists_frequently_lt_of_liminf_ne_top

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem exists_frequently_lt_of_liminf_ne_top' {ι : Type _} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (‖x n‖₊ : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, R < x n :=
  by
  by_contra h
  simp_rw [not_exists, not_frequently, not_lt] at h
  refine'
    hx
      (ENNReal.eq_top_of_forall_nnreal_le fun r =>
        le_Liminf_of_le
          (by
            run_tac
              is_bounded_default)
          _)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)]with i hi using(le_neg.1 hi).trans (neg_le_abs_self _)
#align ennreal.exists_frequently_lt_of_liminf_ne_top' ENNReal.exists_frequently_lt_of_liminf_ne_top'

theorem exists_upcrossings_of_not_bounded_under {ι : Type _} {l : Filter ι} {x : ι → ℝ}
    (hf : liminf (fun i => (‖x i‖₊ : ℝ≥0∞)) l ≠ ∞)
    (hbdd : ¬IsBoundedUnder (· ≤ ·) l fun i => |x i|) :
    ∃ a b : ℚ, a < b ∧ (∃ᶠ i in l, x i < a) ∧ ∃ᶠ i in l, ↑b < x i :=
  by
  rw [is_bounded_under_le_abs, not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine' ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, _, _⟩
    · refine' fun hcon => hR _
      filter_upwards [hcon]with x hx using not_lt.2 (lt_of_lt_of_le hq (not_lt.1 hx)).le
    · simp only [is_bounded_under, is_bounded, eventually_map, eventually_at_top, ge_iff_le,
        not_exists, not_forall, not_le, exists_prop] at hbdd
      refine' fun hcon => hbdd ↑(q + 1) _
      filter_upwards [hcon]with x hx using not_lt.1 hx
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf
    obtain ⟨q, hq⟩ := exists_rat_lt R
    refine' ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, _, _⟩
    · simp only [is_bounded_under, is_bounded, eventually_map, eventually_at_top, ge_iff_le,
        not_exists, not_forall, not_le, exists_prop] at hbdd
      refine' fun hcon => hbdd ↑(q - 1) _
      filter_upwards [hcon]with x hx using not_lt.1 hx
    · refine' fun hcon => hR _
      filter_upwards [hcon]with x hx using not_lt.2 ((not_lt.1 hx).trans hq.le)
#align ennreal.exists_upcrossings_of_not_bounded_under ENNReal.exists_upcrossings_of_not_bounded_under

end Liminf

section tsum

variable {f g : α → ℝ≥0∞}

@[norm_cast]
protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ≥0∞)) ↑r ↔ HasSum f r :=
  by
  have :
    (fun s : Finset α => ∑ a in s, ↑(f a)) =
      (coe : ℝ≥0 → ℝ≥0∞) ∘ fun s : Finset α => ∑ a in s, f a :=
    funext fun s => ENNReal.coe_finset_sum.symm
  unfold HasSum <;> rw [this, tendsto_coe]
#align ennreal.has_sum_coe ENNReal.hasSum_coe

protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : ℝ≥0∞)) = r :=
  (ENNReal.hasSum_coe.2 h).tsum_eq
#align ennreal.tsum_coe_eq ENNReal.tsum_coe_eq

protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : ℝ≥0∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]
#align ennreal.coe_tsum ENNReal.coe_tsum

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_supᵢ fun s t => Finset.sum_le_sum_of_subset
#align ennreal.has_sum ENNReal.hasSum

@[simp]
protected theorem summable : Summable f :=
  ⟨_, ENNReal.hasSum⟩
#align ennreal.summable ENNReal.summable

theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : ℝ≥0∞)) ≠ ∞ ↔ Summable f :=
  by
  refine' ⟨fun h => _, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : ℝ≥0∞) to ℝ≥0 using h with a ha
  refine' ⟨a, ENNReal.hasSum_coe.1 _⟩
  rw [ha]
  exact ennreal.summable.has_sum
#align ennreal.tsum_coe_ne_top_iff_summable ENNReal.tsum_coe_ne_top_iff_summable

protected theorem tsum_eq_supᵢ_sum : (∑' a, f a) = ⨆ s : Finset α, ∑ a in s, f a :=
  ENNReal.hasSum.tsum_eq
#align ennreal.tsum_eq_supr_sum ENNReal.tsum_eq_supᵢ_sum

protected theorem tsum_eq_supᵢ_sum' {ι : Type _} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
    (∑' a, f a) = ⨆ i, ∑ a in s i, f a :=
  by
  rw [ENNReal.tsum_eq_supᵢ_sum]
  symm
  change (⨆ i : ι, (fun t : Finset α => ∑ a in t, f a) (s i)) = ⨆ s : Finset α, ∑ a in s, f a
  exact (Finset.sum_mono_set f).supᵢ_comp_eq hs
#align ennreal.tsum_eq_supr_sum' ENNReal.tsum_eq_supᵢ_sum'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_sigma {β : α → Type _} (f : ∀ a, β a → ℝ≥0∞) :
    (∑' p : Σa, β a, f p.1 p.2) = ∑' (a) (b), f a b :=
  tsum_sigma' (fun b => ENNReal.summable) ENNReal.summable
#align ennreal.tsum_sigma ENNReal.tsum_sigma

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_sigma' {β : α → Type _} (f : (Σa, β a) → ℝ≥0∞) :
    (∑' p : Σa, β a, f p) = ∑' (a) (b), f ⟨a, b⟩ :=
  tsum_sigma' (fun b => ENNReal.summable) ENNReal.summable
#align ennreal.tsum_sigma' ENNReal.tsum_sigma'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_prod {f : α → β → ℝ≥0∞} : (∑' p : α × β, f p.1 p.2) = ∑' (a) (b), f a b :=
  tsum_prod' ENNReal.summable fun _ => ENNReal.summable
#align ennreal.tsum_prod ENNReal.tsum_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
protected theorem tsum_prod' {f : α × β → ℝ≥0∞} : (∑' p : α × β, f p) = ∑' (a) (b), f (a, b) :=
  tsum_prod' ENNReal.summable fun _ => ENNReal.summable
#align ennreal.tsum_prod' ENNReal.tsum_prod'

protected theorem tsum_comm {f : α → β → ℝ≥0∞} : (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b :=
  tsum_comm' ENNReal.summable (fun _ => ENNReal.summable) fun _ => ENNReal.summable
#align ennreal.tsum_comm ENNReal.tsum_comm

protected theorem tsum_add : (∑' a, f a + g a) = (∑' a, f a) + ∑' a, g a :=
  tsum_add ENNReal.summable ENNReal.summable
#align ennreal.tsum_add ENNReal.tsum_add

protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : (∑' a, f a) ≤ ∑' a, g a :=
  tsum_le_tsum h ENNReal.summable ENNReal.summable
#align ennreal.tsum_le_tsum ENNReal.tsum_le_tsum

protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : (∑ x in s, f x) ≤ ∑' x, f x :=
  sum_le_tsum s (fun x hx => zero_le _) ENNReal.summable
#align ennreal.sum_le_tsum ENNReal.sum_le_tsum

protected theorem tsum_eq_supᵢ_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    (∑' i : ℕ, f i) = ⨆ i : ℕ, ∑ a in Finset.range (N i), f a :=
  ENNReal.tsum_eq_supᵢ_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩
#align ennreal.tsum_eq_supr_nat' ENNReal.tsum_eq_supᵢ_nat'

protected theorem tsum_eq_supᵢ_nat {f : ℕ → ℝ≥0∞} :
    (∑' i : ℕ, f i) = ⨆ i : ℕ, ∑ a in Finset.range i, f a :=
  ENNReal.tsum_eq_supᵢ_sum' _ Finset.exists_nat_subset_range
#align ennreal.tsum_eq_supr_nat ENNReal.tsum_eq_supᵢ_nat

protected theorem tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
    (∑' i, f i) = liminf (fun n => ∑ i in Finset.range n, f i) atTop :=
  by
  rw [ENNReal.tsum_eq_supᵢ_nat, Filter.liminf_eq_supᵢ_infᵢ_of_nat]
  congr
  refine' funext fun n => le_antisymm _ _
  · refine' le_infᵢ₂ fun i hi => Finset.sum_le_sum_of_subset_of_nonneg _ fun _ _ _ => zero_le _
    simpa only [Finset.range_subset, add_le_add_iff_right] using hi
  · refine' le_trans (infᵢ_le _ n) _
    simp [le_refl n, le_refl ((Finset.range n).Sum f)]
#align ennreal.tsum_eq_liminf_sum_nat ENNReal.tsum_eq_liminf_sum_nat

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  le_tsum' ENNReal.summable a
#align ennreal.le_tsum ENNReal.le_tsum

@[simp]
protected theorem tsum_eq_zero : (∑' i, f i) = 0 ↔ ∀ i, f i = 0 :=
  ⟨fun h i => nonpos_iff_eq_zero.1 <| h ▸ ENNReal.le_tsum i, fun h => by simp [h]⟩
#align ennreal.tsum_eq_zero ENNReal.tsum_eq_zero

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → (∑' a, f a) = ∞
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a
#align ennreal.tsum_eq_top_of_eq_top ENNReal.tsum_eq_top_of_eq_top

protected theorem lt_top_of_tsum_ne_top {a : α → ℝ≥0∞} (tsum_ne_top : (∑' i, a i) ≠ ∞) (j : α) :
    a j < ∞ := by
  have key := not_imp_not.mpr ENNReal.tsum_eq_top_of_eq_top
  simp only [not_exists] at key
  exact lt_top_iff_ne_top.mpr (key tsum_ne_top j)
#align ennreal.lt_top_of_tsum_ne_top ENNReal.lt_top_of_tsum_ne_top

@[simp]
protected theorem tsum_top [Nonempty α] : (∑' a : α, ∞) = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩
#align ennreal.tsum_top ENNReal.tsum_top

theorem tsum_const_eq_top_of_ne_zero {α : Type _} [Infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∑' a : α, c) = ∞ :=
  by
  have A : tendsto (fun n : ℕ => (n : ℝ≥0∞) * c) at_top (𝓝 (∞ * c)) :=
    by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or_iff, top_ne_zero, Ne.def, not_false_iff]
  have B : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤ ∑' a : α, c :=
    by
    intro n
    rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
    simpa [hs] using @ENNReal.sum_le_tsum α (fun i => c) s
  simpa [hc] using le_of_tendsto' A B
#align ennreal.tsum_const_eq_top_of_ne_zero ENNReal.tsum_const_eq_top_of_ne_zero

protected theorem ne_top_of_tsum_ne_top (h : (∑' a, f a) ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
  h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩
#align ennreal.ne_top_of_tsum_ne_top ENNReal.ne_top_of_tsum_ne_top

protected theorem tsum_mul_left : (∑' i, a * f i) = a * ∑' i, f i :=
  if h : ∀ i, f i = 0 then by simp [h]
  else
    let ⟨i, (hi : f i ≠ 0)⟩ := not_forall.mp h
    have sum_ne_0 : (∑' i, f i) ≠ 0 :=
      ne_of_gt <|
        calc
          0 < f i := lt_of_le_of_ne (zero_le _) hi.symm
          _ ≤ ∑' i, f i := ENNReal.le_tsum _
          
    have : Tendsto (fun s : Finset α => ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      rw [←
          show ((· * ·) a ∘ fun s : Finset α => ∑ j in s, f j) = fun s => ∑ j in s, a * f j from
            funext fun s => Finset.mul_sum] <;>
        exact ENNReal.Tendsto.const_mul ennreal.summable.has_sum (Or.inl sum_ne_0)
    HasSum.tsum_eq this
#align ennreal.tsum_mul_left ENNReal.tsum_mul_left

protected theorem tsum_mul_right : (∑' i, f i * a) = (∑' i, f i) * a := by
  simp [mul_comm, ENNReal.tsum_mul_left]
#align ennreal.tsum_mul_right ENNReal.tsum_mul_right

@[simp]
theorem tsum_supᵢ_eq {α : Type _} (a : α) {f : α → ℝ≥0∞} : (∑' b : α, ⨆ h : a = b, f b) = f a :=
  le_antisymm
    (by
      rw [ENNReal.tsum_eq_supᵢ_sum] <;>
        exact
          supᵢ_le fun s =>
            calc
              (∑ b in s, ⨆ h : a = b, f b) ≤ ∑ b in {a}, ⨆ h : a = b, f b :=
                Finset.sum_le_sum_of_ne_zero fun b _ hb =>
                  suffices a = b by simpa using this.symm
                  by_contradiction fun h => by simpa [h] using hb
              _ = f a := by simp
              )
    (calc
      f a ≤ ⨆ h : a = a, f a := le_supᵢ (fun h : a = a => f a) rfl
      _ ≤ ∑' b : α, ⨆ h : a = b, f b := ENNReal.le_tsum _
      )
#align ennreal.tsum_supr_eq ENNReal.tsum_supᵢ_eq

theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) :=
  by
  refine' ⟨HasSum.tendsto_sum_nat, fun h => _⟩
  rw [← supᵢ_eq_of_tendsto _ h, ← ENNReal.tsum_eq_supᵢ_nat]
  · exact ennreal.summable.has_sum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset.2 hst)
#align ennreal.has_sum_iff_tendsto_nat ENNReal.hasSum_iff_tendsto_nat

theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
    Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n)) :=
  by
  rw [← has_sum_iff_tendsto_nat]
  exact ennreal.summable.has_sum
#align ennreal.tendsto_nat_tsum ENNReal.tendsto_nat_tsum

theorem toNNReal_apply_of_tsum_ne_top {α : Type _} {f : α → ℝ≥0∞} (hf : (∑' i, f i) ≠ ∞) (x : α) :
    (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
  coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _
#align ennreal.to_nnreal_apply_of_tsum_ne_top ENNReal.toNNReal_apply_of_tsum_ne_top

theorem summable_toNNReal_of_tsum_ne_top {α : Type _} {f : α → ℝ≥0∞} (hf : (∑' i, f i) ≠ ∞) :
    Summable (ENNReal.toNNReal ∘ f) := by
  simpa only [← tsum_coe_ne_top_iff_summable, to_nnreal_apply_of_tsum_ne_top hf] using hf
#align ennreal.summable_to_nnreal_of_tsum_ne_top ENNReal.summable_toNNReal_of_tsum_ne_top

theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : (∑' x, f x) ≠ ∞) :
    Tendsto f cofinite (𝓝 0) :=
  by
  have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_to_nnreal (f_ne_top n)).symm
  rw [h_f_coe, ← @coe_zero, tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_to_nnreal_of_tsum_ne_top hf)
#align ennreal.tendsto_cofinite_zero_of_tsum_ne_top ENNReal.tendsto_cofinite_zero_of_tsum_ne_top

theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : (∑' x, f x) ≠ ∞) :
    Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf
#align ennreal.tendsto_at_top_zero_of_tsum_ne_top ENNReal.tendsto_atTop_zero_of_tsum_ne_top

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero {α : Type _} {f : α → ℝ≥0∞} (hf : (∑' x, f x) ≠ ∞) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) :=
  by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  ext1 s
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective
#align ennreal.tendsto_tsum_compl_at_top_zero ENNReal.tendsto_tsum_compl_atTop_zero

protected theorem tsum_apply {ι α : Type _} {f : ι → α → ℝ≥0∞} {x : α} :
    (∑' i, f i) x = ∑' i, f i x :=
  tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable
#align ennreal.tsum_apply ENNReal.tsum_apply

theorem tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : (∑' i, g i) ≠ ∞) (h₂ : g ≤ f) :
    (∑' i, f i - g i) = (∑' i, f i) - ∑' i, g i :=
  by
  have h₃ : (∑' i, f i - g i) = (∑' i, f i - g i + g i) - ∑' i, g i := by
    rw [ENNReal.tsum_add, ENNReal.add_sub_cancel_right h₁]
  have h₄ : (fun i => f i - g i + g i) = f := by
    ext n
    rw [tsub_add_cancel_of_le (h₂ n)]
  rw [h₄] at h₃
  apply h₃
#align ennreal.tsum_sub ENNReal.tsum_sub

theorem tsum_mono_subtype (f : α → ℝ≥0∞) {s t : Set α} (h : s ⊆ t) :
    (∑' x : s, f x) ≤ ∑' x : t, f x :=
  by
  simp only [tsum_subtype]
  apply ENNReal.tsum_le_tsum
  exact indicator_le_indicator_of_subset h fun _ => zero_le _
#align ennreal.tsum_mono_subtype ENNReal.tsum_mono_subtype

theorem tsum_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    (∑' x : s ∪ t, f x) ≤ (∑' x : s, f x) + ∑' x : t, f x :=
  calc
    (∑' x : s ∪ t, f x) = ∑' x : s ∪ t \ s, f x :=
      by
      apply tsum_congr_subtype
      rw [union_diff_self]
    _ = (∑' x : s, f x) + ∑' x : t \ s, f x :=
      (tsum_union_disjoint disjoint_sdiff_self_right ENNReal.summable ENNReal.summable)
    _ ≤ (∑' x : s, f x) + ∑' x : t, f x := add_le_add le_rfl (tsum_mono_subtype _ (diff_subset _ _))
    
#align ennreal.tsum_union_le ENNReal.tsum_union_le

theorem tsum_bUnion_le {ι : Type _} (f : α → ℝ≥0∞) (s : Finset ι) (t : ι → Set α) :
    (∑' x : ⋃ i ∈ s, t i, f x) ≤ ∑ i in s, ∑' x : t i, f x := by
  classical
    induction' s using Finset.induction_on with i s hi ihs h
    · simp
    have : (⋃ j ∈ insert i s, t j) = t i ∪ ⋃ j ∈ s, t j := by simp
    rw [tsum_congr_subtype f this]
    calc
      (∑' x : t i ∪ ⋃ j ∈ s, t j, f x) ≤ (∑' x : t i, f x) + ∑' x : ⋃ j ∈ s, t j, f x :=
        tsum_union_le _ _ _
      _ ≤ (∑' x : t i, f x) + ∑ i in s, ∑' x : t i, f x := (add_le_add le_rfl ihs)
      _ = ∑ j in insert i s, ∑' x : t j, f x := (Finset.sum_insert hi).symm
      
#align ennreal.tsum_bUnion_le ENNReal.tsum_bUnion_le

theorem tsum_unionᵢ_le {ι : Type _} [Fintype ι] (f : α → ℝ≥0∞) (t : ι → Set α) :
    (∑' x : ⋃ i, t i, f x) ≤ ∑ i, ∑' x : t i, f x := by
  classical
    have : (⋃ i, t i) = ⋃ i ∈ (Finset.univ : Finset ι), t i := by simp
    rw [tsum_congr_subtype f this]
    exact tsum_bUnion_le _ _ _
#align ennreal.tsum_Union_le ENNReal.tsum_unionᵢ_le

theorem tsum_eq_add_tsum_ite {f : β → ℝ≥0∞} (b : β) :
    (∑' x, f x) = f b + ∑' x, ite (x = b) 0 (f x) :=
  tsum_eq_add_tsum_ite' b ENNReal.summable
#align ennreal.tsum_eq_add_tsum_ite ENNReal.tsum_eq_add_tsum_ite

theorem tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : (∑' n, f n) = ∞) (hf0 : f 0 ≠ ∞) :
    (∑' n, f (n + 1)) = ∞ :=
  by
  rw [← tsum_eq_tsum_of_hasSum_iff_hasSum fun _ => (notMemRangeEquiv 1).hasSum_iff]
  swap
  · infer_instance
  have h₁ :
    ((∑' b : { n // n ∈ Finset.range 1 }, f b) + ∑' b : { n // n ∉ Finset.range 1 }, f b) =
      ∑' b, f b :=
    tsum_add_tsum_compl ENNReal.summable ENNReal.summable
  rw [Finset.tsum_subtype, Finset.sum_range_one, hf, ENNReal.add_eq_top] at h₁
  rw [← h₁.resolve_left hf0]
  apply tsum_congr
  rintro ⟨i, hi⟩
  simp only [Multiset.mem_range, not_lt] at hi
  simp only [tsub_add_cancel_of_le hi, coe_notMemRangeEquiv, Function.comp_apply, Subtype.coe_mk]
#align ennreal.tsum_add_one_eq_top ENNReal.tsum_add_one_eq_top

/-- A sum of extended nonnegative reals which is finite can have only finitely many terms
above any positive threshold.-/
theorem finite_const_le_of_tsum_ne_top {ι : Type _} {a : ι → ℝ≥0∞} (tsum_ne_top : (∑' i, a i) ≠ ∞)
    {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite :=
  by
  by_cases ε_infty : ε = ∞
  · rw [ε_infty]
    by_contra maybe_infinite
    obtain ⟨j, hj⟩ := Set.Infinite.nonempty maybe_infinite
    exact tsum_ne_top (le_antisymm le_top (le_trans hj (le_tsum' (@ENNReal.summable _ a) j)))
  have key :=
    (nnreal.summable_coe.mpr (summable_to_nnreal_of_tsum_ne_top tsum_ne_top)).tendsto_cofinite_zero
      (Iio_mem_nhds (to_real_pos ε_ne_zero ε_infty))
  simp only [Filter.mem_map, Filter.mem_cofinite, preimage] at key
  have obs : { i : ι | ↑(a i).toNNReal ∈ Iio ε.to_real }ᶜ = { i : ι | ε ≤ a i } :=
    by
    ext i
    simpa only [mem_Iio, mem_compl_iff, mem_set_of_eq, not_lt] using
      to_real_le_to_real ε_infty (ENNReal.ne_top_of_tsum_ne_top tsum_ne_top _)
  rwa [obs] at key
#align ennreal.finite_const_le_of_tsum_ne_top ENNReal.finite_const_le_of_tsum_ne_top

/-- Markov's inequality for `finset.card` and `tsum` in `ℝ≥0∞`. -/
theorem finset_card_const_le_le_of_tsum_le {ι : Type _} {a : ι → ℝ≥0∞} {c : ℝ≥0∞} (c_ne_top : c ≠ ∞)
    (tsum_le_c : (∑' i, a i) ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) :
    ∃ hf : { i : ι | ε ≤ a i }.Finite, ↑hf.toFinset.card ≤ c / ε :=
  by
  by_cases ε = ∞
  · have obs : { i : ι | ε ≤ a i } = ∅ :=
      by
      rw [eq_empty_iff_forall_not_mem]
      intro i hi
      have oops := (le_trans hi (le_tsum' (@ENNReal.summable _ a) i)).trans tsum_le_c
      rw [h] at oops
      exact c_ne_top (le_antisymm le_top oops)
    simp only [obs, finite_empty, finite.to_finset_empty, Finset.card_empty, algebraMap.coe_zero,
      zero_le', exists_true_left]
  have hf : { i : ι | ε ≤ a i }.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (lt_of_le_of_lt tsum_le_c c_ne_top.lt_top).Ne ε_ne_zero
  use hf
  have at_least : ∀ i ∈ hf.to_finset, ε ≤ a i :=
    by
    intro i hi
    simpa only [finite.mem_to_finset, mem_set_of_eq] using hi
  have partial_sum :=
    @sum_le_tsum _ _ _ _ _ a hf.to_finset (fun _ _ => zero_le') (@ENNReal.summable _ a)
  have lower_bound := Finset.sum_le_sum at_least
  simp only [Finset.sum_const, nsmul_eq_mul] at lower_bound
  have key := (ENNReal.le_div_iff_mul_le (Or.inl ε_ne_zero) (Or.inl h)).mpr lower_bound
  exact le_trans key (ENNReal.div_le_div_right (partial_sum.trans tsum_le_c) _)
#align ennreal.finset_card_const_le_le_of_tsum_le ENNReal.finset_card_const_le_le_of_tsum_le

end tsum

theorem tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : fi.Tendsto (fun n => (f n).toReal) (𝓝 x.toReal) ↔ fi.Tendsto f (𝓝 x) :=
  by
  refine' ⟨fun h => _, fun h => tendsto.comp (ENNReal.tendsto_toReal hx) h⟩
  have h_eq : f = fun n => ENNReal.ofReal (f n).toReal :=
    by
    ext1 n
    rw [ENNReal.ofReal_toReal (hf n)]
  rw [h_eq, ← ENNReal.ofReal_toReal hx]
  exact ENNReal.tendsto_ofReal h
#align ennreal.tendsto_to_real_iff ENNReal.tendsto_toReal_iff

theorem tsum_coe_ne_top_iff_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) ≠ ∞ ↔ Summable fun a => (f a : ℝ) :=
  by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable
#align ennreal.tsum_coe_ne_top_iff_summable_coe ENNReal.tsum_coe_ne_top_iff_summable_coe

theorem tsum_coe_eq_top_iff_not_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) = ∞ ↔ ¬Summable fun a => (f a : ℝ) :=
  by
  rw [← @Classical.not_not ((∑' a, ↑(f a)) = ⊤)]
  exact not_congr tsum_coe_ne_top_iff_summable_coe
#align ennreal.tsum_coe_eq_top_iff_not_summable_coe ENNReal.tsum_coe_eq_top_iff_not_summable_coe

theorem hasSum_toReal {f : α → ℝ≥0∞} (hsum : (∑' x, f x) ≠ ∞) :
    HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal) :=
  by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_to_real, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).HasSum
#align ennreal.has_sum_to_real ENNReal.hasSum_toReal

theorem summable_toReal {f : α → ℝ≥0∞} (hsum : (∑' x, f x) ≠ ∞) : Summable fun x => (f x).toReal :=
  (hasSum_toReal hsum).Summable
#align ennreal.summable_to_real ENNReal.summable_toReal

end ENNReal

namespace NNReal

open NNReal

theorem tsum_eq_toNNReal_tsum {f : β → ℝ≥0} : (∑' b, f b) = (∑' b, (f b : ℝ≥0∞)).toNNReal :=
  by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.top_toNNReal, A]
#align nnreal.tsum_eq_to_nnreal_tsum NNReal.tsum_eq_toNNReal_tsum

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem exists_le_hasSum_of_le {f g : β → ℝ≥0} {r : ℝ≥0} (hgf : ∀ b, g b ≤ f b) (hfr : HasSum f r) :
    ∃ p ≤ r, HasSum g p :=
  have : (∑' b, (g b : ℝ≥0∞)) ≤ r :=
    by
    refine' hasSum_le (fun b => _) ennreal.summable.has_sum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
  ⟨p, hpr, ENNReal.hasSum_coe.1 <| Eq ▸ ENNReal.summable.HasSum⟩
#align nnreal.exists_le_has_sum_of_le NNReal.exists_le_hasSum_of_le

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem summable_of_le {f g : β → ℝ≥0} (hgf : ∀ b, g b ≤ f b) : Summable f → Summable g
  | ⟨r, hfr⟩ =>
    let ⟨p, _, hp⟩ := exists_le_hasSum_of_le hgf hfr
    hp.Summable
#align nnreal.summable_of_le NNReal.summable_of_le

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0} {r : ℝ≥0} :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) :=
  by
  rw [← ENNReal.hasSum_coe, ENNReal.hasSum_iff_tendsto_nat]
  simp only [ennreal.coe_finset_sum.symm]
  exact ENNReal.tendsto_coe
#align nnreal.has_sum_iff_tendsto_nat NNReal.hasSum_iff_tendsto_nat

theorem not_summable_iff_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop :=
  by
  constructor
  · intro h
    refine' ((tendsto_of_monotone _).resolve_right h).comp _
    exacts[Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (has_sum_iff_tendsto_nat.1 hr)
#align nnreal.not_summable_iff_tendsto_nat_at_top NNReal.not_summable_iff_tendsto_nat_atTop

theorem summable_iff_not_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_at_top]
#align nnreal.summable_iff_not_tendsto_nat_at_top NNReal.summable_iff_not_tendsto_nat_atTop

theorem summable_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : Summable f :=
  by
  apply summable_iff_not_tendsto_nat_at_top.2 fun H => _
  rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
#align nnreal.summable_of_sum_range_le NNReal.summable_of_sum_range_le

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : (∑' n, f n) ≤ c :=
  tsum_le_of_sum_range_le (summable_of_sum_range_le h) h
#align nnreal.tsum_le_of_sum_range_le NNReal.tsum_le_of_sum_range_le

theorem tsum_comp_le_tsum_of_inj {β : Type _} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : (∑' x, f (i x)) ≤ ∑' x, f x :=
  tsum_le_tsum_of_inj i hi (fun c hc => zero_le _) (fun b => le_rfl) (summable_comp_injective hf hi)
    hf
#align nnreal.tsum_comp_le_tsum_of_inj NNReal.tsum_comp_le_tsum_of_inj

theorem summable_sigma {β : ∀ x : α, Type _} {f : (Σx, β x) → ℝ≥0} :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ :=
  by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.Sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma', ENNReal.coe_tsum,
      h₁] using h₂
#align nnreal.summable_sigma NNReal.summable_sigma

theorem indicator_summable {f : α → ℝ≥0} (hf : Summable f) (s : Set α) : Summable (s.indicator f) :=
  by
  refine' NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) _) hf
  split_ifs
  exact le_refl (f a)
  exact zero_le_coe
#align nnreal.indicator_summable NNReal.indicator_summable

theorem tsum_indicator_ne_zero {f : α → ℝ≥0} (hf : Summable f) {s : Set α} (h : ∃ a ∈ s, f a ≠ 0) :
    (∑' x, (s.indicator f) x) ≠ 0 := fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap
    (trans (Set.indicator_apply_eq_self.mpr (absurd ha)).symm
      (((tsum_eq_zero_iff (indicator_summable hf s)).1 h') a))
#align nnreal.tsum_indicator_ne_zero NNReal.tsum_indicator_ne_zero

open Finset

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) :=
  by
  rw [← tendsto_coe]
  convert tendsto_sum_nat_add fun i => (f i : ℝ)
  norm_cast
#align nnreal.tendsto_sum_nat_add NNReal.tendsto_sum_nat_add

theorem hasSum_lt {f g : α → ℝ≥0} {sf sg : ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg :=
  by
  have A : ∀ a : α, (f a : ℝ) ≤ g a := fun a => NNReal.coe_le_coe.2 (h a)
  have : (sf : ℝ) < sg := hasSum_lt A (NNReal.coe_lt_coe.2 hi) (has_sum_coe.2 hf) (has_sum_coe.2 hg)
  exact NNReal.coe_lt_coe.1 this
#align nnreal.has_sum_lt NNReal.hasSum_lt

@[mono]
theorem hasSum_strict_mono {f g : α → ℝ≥0} {sf sg : ℝ≥0} (hf : HasSum f sf) (hg : HasSum g sg)
    (h : f < g) : sf < sg :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg
#align nnreal.has_sum_strict_mono NNReal.hasSum_strict_mono

theorem tsum_lt_tsum {f g : α → ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hg : Summable g) : (∑' n, f n) < ∑' n, g n :=
  hasSum_lt h hi (summable_of_le h hg).HasSum hg.HasSum
#align nnreal.tsum_lt_tsum NNReal.tsum_lt_tsum

@[mono]
theorem tsum_strict_mono {f g : α → ℝ≥0} (hg : Summable g) (h : f < g) : (∑' n, f n) < ∑' n, g n :=
  let ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg
#align nnreal.tsum_strict_mono NNReal.tsum_strict_mono

theorem tsum_pos {g : α → ℝ≥0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑' b, g b :=
  by
  rw [← tsum_zero]
  exact tsum_lt_tsum (fun a => zero_le _) hi hg
#align nnreal.tsum_pos NNReal.tsum_pos

theorem tsum_eq_add_tsum_ite {f : α → ℝ≥0} (hf : Summable f) (i : α) :
    (∑' x, f x) = f i + ∑' x, ite (x = i) 0 (f x) :=
  by
  refine' tsum_eq_add_tsum_ite' i (NNReal.summable_of_le (fun i' => _) hf)
  rw [Function.update_apply]
  split_ifs <;> simp only [zero_le', le_rfl]
#align nnreal.tsum_eq_add_tsum_ite NNReal.tsum_eq_add_tsum_ite

end NNReal

namespace ENNReal

theorem tsum_toNNReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm
#align ennreal.tsum_to_nnreal_eq ENNReal.tsum_toNNReal_eq

theorem tsum_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toReal = ∑' a, (f a).toReal := by
  simp only [ENNReal.toReal, tsum_to_nnreal_eq hf, NNReal.coe_tsum]
#align ennreal.tsum_to_real_eq ENNReal.tsum_toReal_eq

theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : (∑' i, f i) ≠ ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) :=
  by
  lift f to ℕ → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact_mod_cast NNReal.tendsto_sum_nat_add f
#align ennreal.tendsto_sum_nat_add ENNReal.tendsto_sum_nat_add

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : (∑' n, f n) ≤ c :=
  tsum_le_of_sum_range_le ENNReal.summable h
#align ennreal.tsum_le_of_sum_range_le ENNReal.tsum_le_of_sum_range_le

theorem hasSum_lt {f g : α → ℝ≥0∞} {sf sg : ℝ≥0∞} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hsf : sf ≠ ⊤) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg :=
  by
  by_cases hsg : sg = ⊤
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : ∀ x, g x ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α → ℝ≥0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α → ℝ≥0 using hg'
    lift sf to ℝ≥0 using hsf
    lift sg to ℝ≥0 using hsg
    simp only [coe_le_coe, coe_lt_coe] at h hi⊢
    exact NNReal.hasSum_lt h hi (ENNReal.hasSum_coe.1 hf) (ENNReal.hasSum_coe.1 hg)
#align ennreal.has_sum_lt ENNReal.hasSum_lt

theorem tsum_lt_tsum {f g : α → ℝ≥0∞} {i : α} (hfi : tsum f ≠ ⊤) (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) : (∑' x, f x) < ∑' x, g x :=
  hasSum_lt h hi hfi ENNReal.summable.HasSum ENNReal.summable.HasSum
#align ennreal.tsum_lt_tsum ENNReal.tsum_lt_tsum

end ENNReal

theorem tsum_comp_le_tsum_of_inj {β : Type _} {f : α → ℝ} (hf : Summable f) (hn : ∀ a, 0 ≤ f a)
    {i : β → α} (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f :=
  by
  lift f to α → ℝ≥0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [(· ∘ ·), ← NNReal.coe_tsum] using NNReal.tsum_comp_le_tsum_of_inj hf hi
#align tsum_comp_le_tsum_of_inj tsum_comp_le_tsum_of_inj

/-- Comparison test of convergence of series of non-negative real numbers. -/
theorem summable_of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
    (hf : Summable f) : Summable g :=
  by
  lift f to β → ℝ≥0 using fun b => (hg b).trans (hgf b)
  lift g to β → ℝ≥0 using hg
  rw [NNReal.summable_coe] at hf⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf
#align summable_of_nonneg_of_le summable_of_nonneg_of_le

theorem Summable.toNNReal {f : α → ℝ} (hf : Summable f) : Summable fun n => (f n).toNNReal :=
  by
  apply NNReal.summable_coe.1
  refine' summable_of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => _) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]
#align summable.to_nnreal Summable.toNNReal

/-- A series of non-negative real numbers converges to `r` in the sense of `has_sum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) :=
  by
  lift f to ℕ → ℝ≥0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat
#align has_sum_iff_tendsto_nat_of_nonneg hasSum_iff_tendsto_nat_of_nonneg

theorem ENNReal.ofReal_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n) := by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]
#align ennreal.of_real_tsum_of_nonneg ENNReal.ofReal_tsum_of_nonneg

theorem not_summable_iff_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop :=
  by
  lift f to ℕ → ℝ≥0 using hf
  exact_mod_cast NNReal.not_summable_iff_tendsto_nat_atTop
#align not_summable_iff_tendsto_nat_at_top_of_nonneg not_summable_iff_tendsto_nat_atTop_of_nonneg

theorem summable_iff_not_tendsto_nat_atTop_of_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop_of_nonneg hf]
#align summable_iff_not_tendsto_nat_at_top_of_nonneg summable_iff_not_tendsto_nat_atTop_of_nonneg

theorem summable_sigma_of_nonneg {β : ∀ x : α, Type _} {f : (Σx, β x) → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ :=
  by
  lift f to (Σx, β x) → ℝ≥0 using hf
  exact_mod_cast NNReal.summable_sigma
#align summable_sigma_of_nonneg summable_sigma_of_nonneg

theorem summable_of_sum_le {ι : Type _} {f : ι → ℝ} {c : ℝ} (hf : 0 ≤ f)
    (h : ∀ u : Finset ι, (∑ x in u, f x) ≤ c) : Summable f :=
  ⟨⨆ u : Finset ι, ∑ x in u, f x,
    tendsto_atTop_csupr (Finset.sum_mono_set_of_nonneg hf) ⟨c, fun y ⟨u, hu⟩ => hu ▸ h u⟩⟩
#align summable_of_sum_le summable_of_sum_le

theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : Summable f :=
  by
  apply (summable_iff_not_tendsto_nat_atTop_of_nonneg hf).2 fun H => _
  rcases exists_lt_of_tendsto_at_top H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))
#align summable_of_sum_range_le summable_of_sum_range_le

theorem Real.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ n, (∑ i in Finset.range n, f i) ≤ c) : (∑' n, f n) ≤ c :=
  tsum_le_of_sum_range_le (summable_of_sum_range_le hf h) h
#align real.tsum_le_of_sum_range_le Real.tsum_le_of_sum_range_le

/-- If a sequence `f` with non-negative terms is dominated by a sequence `g` with summable
series and at least one term of `f` is strictly smaller than the corresponding term in `g`,
then the series of `f` is strictly smaller than the series of `g`. -/
theorem tsum_lt_tsum_of_nonneg {i : ℕ} {f g : ℕ → ℝ} (h0 : ∀ b : ℕ, 0 ≤ f b)
    (h : ∀ b : ℕ, f b ≤ g b) (hi : f i < g i) (hg : Summable g) : (∑' n, f n) < ∑' n, g n :=
  tsum_lt_tsum h hi (summable_of_nonneg_of_le h0 h hg) hg
#align tsum_lt_tsum_of_nonneg tsum_lt_tsum_of_nonneg

section

variable [EMetricSpace β]

open ENNReal Filter Emetric

/-- In an emetric ball, the distance between points is everywhere finite -/
theorem edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : ball a r) : edist x.1 y.1 ≠ ⊤ :=
  lt_top_iff_ne_top.1 <|
    calc
      edist x y ≤ edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y] <;> exact add_lt_add x.2 y.2
      _ ≤ ⊤ := le_top
      
#align edist_ne_top_of_mem_ball edist_ne_top_of_mem_ball

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metricSpaceEmetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (ball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball
#align metric_space_emetric_ball metricSpaceEmetricBall

attribute [local instance] metricSpaceEmetricBall

theorem nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ ball a r) :
    𝓝 x = map (coe : ball a r → β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq_nhds _ <| IsOpen.mem_nhds EMetric.isOpen_ball h).symm
#align nhds_eq_nhds_emetric_ball nhds_eq_nhds_emetric_ball

end

section

variable [PseudoEMetricSpace α]

open Emetric

theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β → α} {y : α} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0) := by
  simp only [emetric.nhds_basis_eball.tendsto_right_iff, EMetric.mem_ball,
    @tendsto_order ℝ≥0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and_iff]
#align tendsto_iff_edist_tendsto_0 tendsto_iff_edist_tendsto_0

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem Emetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β → α} :
    CauchySeq s ↔
      ∃ b : β → ℝ≥0∞,
        (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N) ∧ Tendsto b atTop (𝓝 0) :=
  ⟨by
    intro hs
    rw [EMetric.cauchySeq_iff] at hs
    /- `s` is Cauchy sequence. The sequence `b` will be constructed by taking
      the supremum of the distances between `s n` and `s m` for `n m ≥ N`-/
    let b N := Sup ((fun p : β × β => edist (s p.1) (s p.2)) '' { p | p.1 ≥ N ∧ p.2 ≥ N })
    --Prove that it bounds the distances of points in the Cauchy sequence
    have C : ∀ n m N, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N :=
      by
      refine' fun m n N hm hn => le_supₛ _
      use Prod.mk m n
      simp only [and_true_iff, eq_self_iff_true, Set.mem_setOf_eq]
      exact ⟨hm, hn⟩
    --Prove that it tends to `0`, by using the Cauchy property of `s`
    have D : tendsto b at_top (𝓝 0) :=
      by
      refine' tendsto_order.2 ⟨fun a ha => absurd ha ENNReal.not_lt_zero, fun ε εpos => _⟩
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      rcases hs δ δpos with ⟨N, hN⟩
      refine' Filter.mem_atTop_sets.2 ⟨N, fun n hn => _⟩
      have : b n ≤ δ :=
        supₛ_le
          (by
            simp only [and_imp, Set.mem_image, Set.mem_setOf_eq, exists_imp, Prod.exists]
            intro d p q hp hq hd
            rw [← hd]
            exact le_of_lt (hN p (le_trans hn hp) q (le_trans hn hq)))
      simpa using lt_of_le_of_lt this δlt
    -- Conclude
    exact ⟨b, ⟨C, D⟩⟩,
    by
    rintro ⟨b, ⟨b_bound, b_lim⟩⟩
    /-b : ℕ → ℝ, b_bound : ∀ (n m N : ℕ), N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N,
        b_lim : tendsto b at_top (𝓝 0)-/
    refine' EMetric.cauchySeq_iff.2 fun ε εpos => _
    have : ∀ᶠ n in at_top, b n < ε := (tendsto_order.1 b_lim).2 _ εpos
    rcases Filter.mem_atTop_sets.1 this with ⟨N, hN⟩
    exact
      ⟨N, fun m hm n hn =>
        calc
          edist (s m) (s n) ≤ b N := b_bound m n N hm hn
          _ < ε := hN _ (le_refl N)
          ⟩⟩
#align emetric.cauchy_seq_iff_le_tendsto_0 Emetric.cauchySeq_iff_le_tendsto_0

theorem continuous_of_le_add_edist {f : α → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ x y, f x ≤ f y + C * edist x y) : Continuous f :=
  by
  rcases eq_or_ne C 0 with (rfl | C0)
  · simp only [zero_mul, add_zero] at h
    exact continuous_of_const fun x y => le_antisymm (h _ _) (h _ _)
  · refine' continuous_iff_continuousAt.2 fun x => _
    by_cases hx : f x = ∞
    · have : f =ᶠ[𝓝 x] fun _ => ∞ :=
        by
        filter_upwards [EMetric.ball_mem_nhds x ENNReal.coe_lt_top]
        refine' fun y (hy : edist y x < ⊤) => _
        rw [edist_comm] at hy
        simpa [hx, ENNReal.mul_ne_top hC hy.ne] using h x y
      exact this.continuous_at
    · refine' (ENNReal.tendsto_nhds hx).2 fun ε (ε0 : 0 < ε) => _
      filter_upwards [EMetric.closedBall_mem_nhds x (ENNReal.div_pos_iff.2 ⟨ε0.ne', hC⟩)]
      have hεC : C * (ε / C) = ε := ENNReal.mul_div_cancel' C0 hC
      refine' fun y (hy : edist y x ≤ ε / C) => ⟨tsub_le_iff_right.2 _, _⟩
      · rw [edist_comm] at hy
        calc
          f x ≤ f y + C * edist x y := h x y
          _ ≤ f y + C * (ε / C) := (add_le_add_left (mul_le_mul_left' hy C) (f y))
          _ = f y + ε := by rw [hεC]
          
      ·
        calc
          f y ≤ f x + C * edist y x := h y x
          _ ≤ f x + C * (ε / C) := (add_le_add_left (mul_le_mul_left' hy C) (f x))
          _ = f x + ε := by rw [hεC]
          
#align continuous_of_le_add_edist continuous_of_le_add_edist

theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 :=
  by
  apply continuous_of_le_add_edist 2 (by norm_num)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y ≤ edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by simp [edist_comm] <;> cc
    _ ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) :=
      (add_le_add_left (add_le_add (le_max_left _ _) (le_max_right _ _)) _)
    _ = edist x' y' + 2 * edist (x, y) (x', y') := by rw [← mul_two, mul_comm]
    
#align continuous_edist continuous_edist

@[continuity]
theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prod_mk hg : _)
#align continuous.edist Continuous.edist

theorem Filter.Tendsto.edist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.Tendsto (a, b)).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.edist Filter.Tendsto.edist

theorem cauchySeq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) : CauchySeq f :=
  by
  lift d to ℕ → NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd
#align cauchy_seq_of_edist_le_of_tsum_ne_top cauchySeq_of_edist_le_of_tsum_ne_top

theorem Emetric.isClosed_ball {a : α} {r : ℝ≥0∞} : IsClosed (closedBall a r) :=
  isClosed_le (continuous_id.edist continuous_const) continuous_const
#align emetric.is_closed_ball Emetric.isClosed_ball

@[simp]
theorem Emetric.diam_closure (s : Set α) : diam (closure s) = diam s :=
  by
  refine' le_antisymm (diam_le fun x hx y hy => _) (diam_mono subset_closure)
  have : edist x y ∈ closure (Iic (diam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_diam_of_mem hx hy
  rwa [closure_Iic] at this
#align emetric.diam_closure Emetric.diam_closure

@[simp]
theorem Metric.diam_closure {α : Type _} [PseudoMetricSpace α] (s : Set α) :
    Metric.diam (closure s) = diam s := by simp only [Metric.diam, Emetric.diam_closure]
#align metric.diam_closure Metric.diam_closure

theorem isClosed_setOf_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0)
    (s : Set α) : IsClosed { f : α → β | LipschitzOnWith K f s } :=
  by
  simp only [LipschitzOnWith, set_of_forall]
  refine' isClosed_binterᵢ fun x hx => isClosed_binterᵢ fun y hy => isClosed_le _ _
  exacts[Continuous.edist (continuous_apply x) (continuous_apply y), continuous_const]
#align is_closed_set_of_lipschitz_on_with isClosed_setOf_lipschitzOnWith

theorem isClosed_setOf_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) :
    IsClosed { f : α → β | LipschitzWith K f } := by
  simp only [← lipschitz_on_univ, isClosed_setOf_lipschitzOnWith]
#align is_closed_set_of_lipschitz_with isClosed_setOf_lipschitzWith

namespace Real

/-- For a bounded set `s : set ℝ`, its `emetric.diam` is equal to `Sup s - Inf s` reinterpreted as
`ℝ≥0∞`. -/
theorem ediam_eq {s : Set ℝ} (h : Bounded s) : EMetric.diam s = ENNReal.ofReal (supₛ s - infₛ s) :=
  by
  rcases eq_empty_or_nonempty s with (rfl | hne); · simp
  refine' le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => _) _
  · have := Real.subset_Icc_infₛ_supₛ_of_bounded h
    exact Real.dist_le_of_mem_Icc (this hx) (this hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam, ← Metric.diam_closure]
    have h' := Real.bounded_iff_bddBelow_bddAbove.1 h
    calc
      Sup s - Inf s ≤ dist (Sup s) (Inf s) := le_abs_self _
      _ ≤ diam (closure s) :=
        dist_le_diam_of_mem h.closure (csupₛ_mem_closure hne h'.2) (cinfₛ_mem_closure hne h'.1)
      
#align real.ediam_eq Real.ediam_eq

/-- For a bounded set `s : set ℝ`, its `metric.diam` is equal to `Sup s - Inf s`. -/
theorem diam_eq {s : Set ℝ} (h : Bounded s) : Metric.diam s = supₛ s - infₛ s :=
  by
  rw [Metric.diam, Real.ediam_eq h, ENNReal.toReal_ofReal]
  rw [Real.bounded_iff_bddBelow_bddAbove] at h
  exact sub_nonneg.2 (Real.infₛ_le_supₛ s h.1 h.2)
#align real.diam_eq Real.diam_eq

@[simp]
theorem ediam_Ioo (a b : ℝ) : EMetric.diam (Ioo a b) = ENNReal.ofReal (b - a) :=
  by
  rcases le_or_lt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (bounded_Ioo _ _), csupₛ_Ioo h, cinfₛ_Ioo h]
#align real.ediam_Ioo Real.ediam_Ioo

@[simp]
theorem ediam_Icc (a b : ℝ) : EMetric.diam (Icc a b) = ENNReal.ofReal (b - a) :=
  by
  rcases le_or_lt a b with (h | h)
  · rw [Real.ediam_eq (bounded_Icc _ _), csupₛ_Icc h, cinfₛ_Icc h]
  · simp [h, h.le]
#align real.ediam_Icc Real.ediam_Icc

@[simp]
theorem ediam_Ico (a b : ℝ) : EMetric.diam (Ico a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ diam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ico_self)
#align real.ediam_Ico Real.ediam_Ico

@[simp]
theorem ediam_Ioc (a b : ℝ) : EMetric.diam (Ioc a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ diam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ioc_self)
#align real.ediam_Ioc Real.ediam_Ioc

theorem diam_Icc {a b : ℝ} (h : a ≤ b) : Metric.diam (Icc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Icc Real.diam_Icc

theorem diam_Ico {a b : ℝ} (h : a ≤ b) : Metric.diam (Ico a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Ico Real.diam_Ico

theorem diam_Ioc {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Ioc Real.diam_Ioc

theorem diam_Ioo {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioo a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal, sub_nonneg.2 h]
#align real.diam_Ioo Real.diam_Ioo

end Real

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ ∑' m, d (n + m) :=
  by
  refine' le_of_tendsto (tendsto_const_nhds.edist ha) (mem_at_top_sets.2 ⟨n, fun m hnm => _⟩)
  refine' le_trans (edist_le_Ico_sum_of_edist_le hnm fun k _ _ => hf k) _
  rw [Finset.sum_Ico_eq_sum_range]
  exact sum_le_tsum _ (fun _ _ => zero_le _) ENNReal.summable
#align edist_le_tsum_of_edist_le_of_tendsto edist_le_tsum_of_edist_le_of_tendsto

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ ∑' m, d m := by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0
#align edist_le_tsum_of_edist_le_of_tendsto₀ edist_le_tsum_of_edist_le_of_tendsto₀

end

--section
