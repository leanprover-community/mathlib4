/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.instances.ereal
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Encodable
import Mathbin.Data.Real.Ereal
import Mathbin.Topology.Algebra.Order.MonotoneContinuity
import Mathbin.Topology.Instances.Ennreal

/-!
# Topological structure on `ereal`

We endow `ereal` with the order topology, and prove basic properties of this topology.

## Main results

* `coe : ℝ → ereal` is an open embedding
* `coe : ℝ≥0∞ → ereal` is an embedding
* The addition on `ereal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `ereal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/


noncomputable section

open Classical Set Filter Metric TopologicalSpace

open Classical Topology ENNReal NNReal BigOperators Filter

variable {α : Type _} [TopologicalSpace α]

namespace EReal

instance : TopologicalSpace EReal :=
  Preorder.topology EReal

instance : OrderTopology EReal :=
  ⟨rfl⟩

instance : T2Space EReal := by infer_instance

instance : SecondCountableTopology EReal :=
  ⟨by
    refine'
      ⟨⋃ q : ℚ, {{ a : EReal | a < (q : ℝ) }, { a : EReal | ((q : ℝ) : EReal) < a }},
        countable_Union fun a => (countable_singleton _).insert _, _⟩
    refine'
      le_antisymm
        (le_generateFrom <| by
          simp (config := { contextual := true }) [or_imp, isOpen_lt', isOpen_gt'])
        _
    apply le_generateFrom fun s h => _
    rcases h with ⟨a, hs | hs⟩ <;>
        [rw [show s = ⋃ q ∈ { q : ℚ | a < (q : ℝ) }, { b | ((q : ℝ) : EReal) < b }
            by
            ext x
            simpa only [hs, exists_prop, mem_Union] using lt_iff_exists_rat_btwn],
        rw [show s = ⋃ q ∈ { q : ℚ | ((q : ℝ) : EReal) < a }, { b | b < ((q : ℝ) : EReal) }
            by
            ext x
            simpa only [hs, and_comm', exists_prop, mem_Union] using lt_iff_exists_rat_btwn]] <;>
      · apply isOpen_unionᵢ
        intro q
        apply isOpen_unionᵢ
        intro hq
        apply generate_open.basic
        exact mem_Union.2 ⟨q, by simp⟩⟩

/-! ### Real coercion -/


theorem embedding_coe : Embedding (coe : ℝ → EReal) :=
  ⟨⟨by
      refine' le_antisymm _ _
      · rw [@OrderTopology.topology_eq_generate_intervals EReal _, ← coinduced_le_iff_le_induced]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        show IsOpen { b : ℝ | a < ↑b }
        · induction a using EReal.rec
          · simp only [isOpen_univ, bot_lt_coe, set_of_true]
          · simp only [EReal.coe_lt_coe_iff]
            exact isOpen_Ioi
          · simp only [set_of_false, isOpen_empty, not_top_lt]
        show IsOpen { b : ℝ | ↑b < a }
        · induction a using EReal.rec
          · simp only [not_lt_bot, set_of_false, isOpen_empty]
          · simp only [EReal.coe_lt_coe_iff]
            exact isOpen_Iio
          · simp only [isOpen_univ, coe_lt_top, set_of_true]
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ _]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        exact ⟨Ioi a, isOpen_Ioi, by simp [Ioi]⟩
        exact ⟨Iio a, isOpen_Iio, by simp [Iio]⟩⟩, fun a b => by
    simp only [imp_self, EReal.coe_eq_coe_iff]⟩
#align ereal.embedding_coe EReal.embedding_coe

theorem openEmbedding_coe : OpenEmbedding (coe : ℝ → EReal) :=
  ⟨embedding_coe, by
    convert @isOpen_Ioo EReal _ _ _ ⊥ ⊤
    ext x
    induction x using EReal.rec
    · simp only [left_mem_Ioo, mem_range, coe_ne_bot, exists_false, not_false_iff]
    · simp only [mem_range_self, mem_Ioo, bot_lt_coe, coe_lt_top, and_self_iff]
    · simp only [mem_range, right_mem_Ioo, exists_false, coe_ne_top]⟩
#align ereal.open_embedding_coe EReal.openEmbedding_coe

@[norm_cast]
theorem tendsto_coe {α : Type _} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm
#align ereal.tendsto_coe EReal.tendsto_coe

theorem continuous_coe_real_eReal : Continuous (coe : ℝ → EReal) :=
  embedding_coe.Continuous
#align continuous_coe_real_ereal continuous_coe_real_eReal

theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm
#align ereal.continuous_coe_iff EReal.continuous_coe_iff

theorem nhds_coe {r : ℝ} : 𝓝 (r : EReal) = (𝓝 r).map coe :=
  (openEmbedding_coe.map_nhds_eq r).symm
#align ereal.nhds_coe EReal.nhds_coe

theorem nhds_coe_coe {r p : ℝ} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (p.1, p.2) :=
  ((openEmbedding_coe.Prod openEmbedding_coe).map_nhds_eq (r, p)).symm
#align ereal.nhds_coe_coe EReal.nhds_coe_coe

theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  by
  lift a to ℝ using And.intro ha h'a
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
#align ereal.tendsto_to_real EReal.tendsto_toReal

theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun a ha =>
  ContinuousAt.continuousWithinAt
    (tendsto_toReal
      (by
        simp [not_or] at ha
        exact ha.2)
      (by
        simp [not_or] at ha
        exact ha.1))
#align ereal.continuous_on_to_real EReal.continuousOn_toReal

/-- The set of finite `ereal` numbers is homeomorphic to `ℝ`. -/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ :=
  {
    neTopBotEquivReal with
    continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toReal
    continuous_invFun := continuous_coe_real_eReal.subtype_mk _ }
#align ereal.ne_bot_top_homeomorph_real EReal.neBotTopHomeomorphReal

/-! ### ennreal coercion -/


theorem embedding_coe_eNNReal : Embedding (coe : ℝ≥0∞ → EReal) :=
  ⟨⟨by
      refine' le_antisymm _ _
      · rw [@OrderTopology.topology_eq_generate_intervals EReal _, ← coinduced_le_iff_le_induced]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        show IsOpen { b : ℝ≥0∞ | a < ↑b }
        · induction' a using EReal.rec with x
          · simp only [isOpen_univ, bot_lt_coe_ennreal, set_of_true]
          · rcases le_or_lt 0 x with (h | h)
            · have : (x : EReal) = ((id ⟨x, h⟩ : ℝ≥0) : ℝ≥0∞) := rfl
              rw [this]
              simp only [id.def, coe_ennreal_lt_coe_ennreal_iff]
              exact isOpen_Ioi
            · have : ∀ y : ℝ≥0∞, (x : EReal) < y := fun y =>
                (EReal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg _)
              simp only [this, isOpen_univ, set_of_true]
          · simp only [set_of_false, isOpen_empty, not_top_lt]
        show IsOpen { b : ℝ≥0∞ | ↑b < a }
        · induction' a using EReal.rec with x
          · simp only [not_lt_bot, set_of_false, isOpen_empty]
          · rcases le_or_lt 0 x with (h | h)
            · have : (x : EReal) = ((id ⟨x, h⟩ : ℝ≥0) : ℝ≥0∞) := rfl
              rw [this]
              simp only [id.def, coe_ennreal_lt_coe_ennreal_iff]
              exact isOpen_Iio
            · convert isOpen_empty
              apply eq_empty_iff_forall_not_mem.2 fun y hy => lt_irrefl (x : EReal) _
              exact ((EReal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg y)).trans hy
          · simp only [← coe_ennreal_top, coe_ennreal_lt_coe_ennreal_iff]
            exact isOpen_Iio
      · rw [@OrderTopology.topology_eq_generate_intervals ℝ≥0∞ _]
        refine' le_generateFrom fun s ha => _
        rcases ha with ⟨a, rfl | rfl⟩
        exact ⟨Ioi a, isOpen_Ioi, by simp [Ioi]⟩
        exact ⟨Iio a, isOpen_Iio, by simp [Iio]⟩⟩, fun a b => by
    simp only [imp_self, coe_ennreal_eq_coe_ennreal_iff]⟩
#align ereal.embedding_coe_ennreal EReal.embedding_coe_eNNReal

@[norm_cast]
theorem tendsto_coe_eNNReal {α : Type _} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe_eNNReal.tendsto_nhds_iff.symm
#align ereal.tendsto_coe_ennreal EReal.tendsto_coe_eNNReal

theorem continuous_coe_eNNReal_eReal : Continuous (coe : ℝ≥0∞ → EReal) :=
  embedding_coe_eNNReal.Continuous
#align continuous_coe_ennreal_ereal continuous_coe_eNNReal_eReal

theorem continuous_coe_eNNReal_iff {f : α → ℝ≥0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe_eNNReal.continuous_iff.symm
#align ereal.continuous_coe_ennreal_iff EReal.continuous_coe_eNNReal_iff

/-! ### Neighborhoods of infinity -/


/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » «expr⊤»()) -/
theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]
#align ereal.nhds_top EReal.nhds_top

theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi a) :=
  by
  rw [nhds_top]
  apply le_antisymm
  · exact infᵢ_mono' fun x => ⟨x, by simp⟩
  · refine' le_infᵢ fun r => le_infᵢ fun hr => _
    induction r using EReal.rec
    · exact (infᵢ_le _ 0).trans (by simp)
    · exact infᵢ_le _ _
    · simpa using hr
#align ereal.nhds_top' EReal.nhds_top'

theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s :=
  by
  rw [nhds_top', mem_infi_of_directed]
  · rfl
  exact fun x y => ⟨max x y, by simp [le_refl], by simp [le_refl]⟩
#align ereal.mem_nhds_top_iff EReal.mem_nhds_top_iff

theorem tendsto_nhds_top_iff_real {α : Type _} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', mem_Ioi, tendsto_infi, tendsto_principal]
#align ereal.tendsto_nhds_top_iff_real EReal.tendsto_nhds_top_iff_real

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (a «expr ≠ » «expr⊥»()) -/
theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [bot_lt_iff_ne_bot]
#align ereal.nhds_bot EReal.nhds_bot

theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : ℝ, 𝓟 (Iio a) :=
  by
  rw [nhds_bot]
  apply le_antisymm
  · exact infᵢ_mono' fun x => ⟨x, by simp⟩
  · refine' le_infᵢ fun r => le_infᵢ fun hr => _
    induction r using EReal.rec
    · simpa using hr
    · exact infᵢ_le _ _
    · exact (infᵢ_le _ 0).trans (by simp)
#align ereal.nhds_bot' EReal.nhds_bot'

theorem mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 (⊥ : EReal) ↔ ∃ y : ℝ, Iio (y : EReal) ⊆ s :=
  by
  rw [nhds_bot', mem_infi_of_directed]
  · rfl
  exact fun x y => ⟨min x y, by simp [le_refl], by simp [le_refl]⟩
#align ereal.mem_nhds_bot_iff EReal.mem_nhds_bot_iff

theorem tendsto_nhds_bot_iff_real {α : Type _} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x := by
  simp only [nhds_bot', mem_Iio, tendsto_infi, tendsto_principal]
#align ereal.tendsto_nhds_bot_iff_real EReal.tendsto_nhds_bot_iff_real

/-! ### Continuity of addition -/


theorem continuousAt_add_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (· ∘ ·), tendsto_coe,
    tendsto_add]
#align ereal.continuous_at_add_coe_coe EReal.continuousAt_add_coe_coe

theorem continuousAt_add_top_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) :=
  by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe, nhds_prod_eq]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => ((r - (a - 1) : ℝ) : EReal) < z, Ioi_mem_nhds (coe_lt_top _), fun z =>
      ((a - 1 : ℝ) : EReal) < z, Ioi_mem_nhds (by simp [-EReal.coe_sub]), fun x hx y hy => _⟩
  dsimp
  convert add_lt_add hx hy
  simp
#align ereal.continuous_at_add_top_coe EReal.continuousAt_add_top_coe

theorem continuousAt_add_coe_top (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) :=
  by
  change ContinuousAt ((fun p : EReal × EReal => p.2 + p.1) ∘ Prod.swap) (a, ⊤)
  apply ContinuousAt.comp _ continuous_swap.continuous_at
  simp_rw [add_comm]
  exact continuous_at_add_top_coe a
#align ereal.continuous_at_add_coe_top EReal.continuousAt_add_coe_top

theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) :=
  by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top, nhds_prod_eq]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => (r : EReal) < z, Ioi_mem_nhds (coe_lt_top _), fun z => ((0 : ℝ) : EReal) < z,
      Ioi_mem_nhds (by simp [zero_lt_one]), fun x hx y hy => _⟩
  dsimp
  convert add_lt_add hx hy
  simp
#align ereal.continuous_at_add_top_top EReal.continuousAt_add_top_top

theorem continuousAt_add_bot_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) :=
  by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => z < ((r - (a + 1) : ℝ) : EReal), Iio_mem_nhds (bot_lt_coe _), fun z =>
      z < ((a + 1 : ℝ) : EReal), Iio_mem_nhds (by simp [-coe_add, zero_lt_one]), fun x hx y hy => _⟩
  convert add_lt_add hx hy
  rw [sub_add_cancel]
#align ereal.continuous_at_add_bot_coe EReal.continuousAt_add_bot_coe

theorem continuousAt_add_coe_bot (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) :=
  by
  change ContinuousAt ((fun p : EReal × EReal => p.2 + p.1) ∘ Prod.swap) (a, ⊥)
  apply ContinuousAt.comp _ continuous_swap.continuous_at
  simp_rw [add_comm]
  exact continuous_at_add_bot_coe a
#align ereal.continuous_at_add_coe_bot EReal.continuousAt_add_coe_bot

theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) :=
  by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add]
  intro r
  rw [eventually_prod_iff]
  refine'
    ⟨fun z => z < r, Iio_mem_nhds (bot_lt_coe _), fun z => z < 0, Iio_mem_nhds (bot_lt_coe _),
      fun x hx y hy => _⟩
  dsimp
  convert add_lt_add hx hy
  simp
#align ereal.continuous_at_add_bot_bot EReal.continuousAt_add_bot_bot

/-- The addition on `ereal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
theorem continuousAt_add {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p :=
  by
  rcases p with ⟨x, y⟩
  induction x using EReal.rec <;> induction y using EReal.rec
  · exact continuous_at_add_bot_bot
  · exact continuous_at_add_bot_coe _
  · simpa using h'
  · exact continuous_at_add_coe_bot _
  · exact continuous_at_add_coe_coe _ _
  · exact continuous_at_add_coe_top _
  · simpa using h
  · exact continuous_at_add_top_coe _
  · exact continuous_at_add_top_top
#align ereal.continuous_at_add EReal.continuousAt_add

/-! ### Negation-/


/-- Negation on `ereal` as a homeomorphism -/
def negHomeo : EReal ≃ₜ EReal :=
  negOrderIso.toHomeomorph
#align ereal.neg_homeo EReal.negHomeo

theorem continuous_neg : Continuous fun x : EReal => -x :=
  negHomeo.Continuous
#align ereal.continuous_neg EReal.continuous_neg

end EReal

