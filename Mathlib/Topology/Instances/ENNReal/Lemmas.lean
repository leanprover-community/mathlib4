/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Bound
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Topology on extended non-negative reals
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

theorem isOpen_ne_top : IsOpen { a : ℝ≥0∞ | a ≠ ∞ } := isOpen_ne

theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio

theorem coe_range_mem_nhds : range ((↑) : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range <| mem_range_self _

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ≥0∞) :=
  isEmbedding_coe.continuous

lemma tendsto_coe_toNNReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto (↑) (𝓝 a.toNNReal) (𝓝 a) := by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact continuous_coe.tendsto _

theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℝ≥0} :
    (Continuous fun a => (f a : ℝ≥0∞)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm

theorem nhds_coe {r : ℝ≥0} : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

theorem tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : ℝ≥0 → α) (𝓝 x) l := by
  rw [nhds_coe, tendsto_map'_iff]

theorem continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : ℝ≥0 → α) x :=
  tendsto_nhds_coe_iff

theorem continuous_ofReal : Continuous ENNReal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal

theorem tendsto_ofReal {f : Filter α} {m : α → ℝ} {a : ℝ} (h : Tendsto m f (𝓝 a)) :
    Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a)) :=
  (continuous_ofReal.tendsto a).comp h

theorem tendsto_toNNReal {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal) := by
  lift a to ℝ≥0 using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

theorem tendsto_toNNReal_iff {f : α → ℝ≥0∞} {u : Filter α} (ha : a ≠ ∞) (hf : ∀ x, f x ≠ ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 (a.toNNReal)) ↔ Tendsto f u (𝓝 a) := by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toNNReal ha).comp h⟩
  rw [← coe_comp_toNNReal_comp hf]
  exact (tendsto_coe_toNNReal ha).comp h

theorem tendsto_toNNReal_iff' {f : α → ℝ≥0∞} {u : Filter α} {a : ℝ≥0} (hf : ∀ x, f x ≠ ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 a) ↔ Tendsto f u (𝓝 a) := by
  rw [← toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf

theorem eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α → ℝ≥0∞}
    (hfi : ∀ᶠ x in l, f x ≠ ∞) (hgi : ∀ᶠ x in l, g x ≠ ∞)
    (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g := by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal hfx hgx]

theorem continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a ≠ ∞ } := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)

theorem tendsto_toReal {a : ℝ≥0∞} (ha : a ≠ ∞) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  NNReal.tendsto_coe.2 <| tendsto_toNNReal ha

lemma continuousOn_toReal : ContinuousOn ENNReal.toReal { a | a ≠ ∞ } :=
  NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal

lemma continuousAt_toReal (hx : x ≠ ∞) : ContinuousAt ENNReal.toReal x :=
  continuousOn_toReal.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def neTopHomeomorphNNReal : { a | a ≠ ∞ } ≃ₜ ℝ≥0 where
  toEquiv := neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ ℝ≥0 := by
  refine (Homeomorph.setCongr ?_).trans neTopHomeomorphNNReal
  simp only [lt_top_iff_ne_top]

theorem nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a ≠ ∞), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]

theorem nhds_top' : 𝓝 ∞ = ⨅ r : ℝ≥0, 𝓟 (Ioi ↑r) :=
  nhds_top.trans <| iInf_ne_top _

theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  _root_.nhds_top_basis

theorem tendsto_nhds_top_iff_nnreal {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ ∀ x : ℝ≥0, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]

theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a :=
  tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_natCast] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
      (h n).mono fun _ => lt_trans <| by rwa [← ENNReal.coe_natCast, coe_lt_coe]⟩

theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) :
    Tendsto m f (𝓝 ∞) :=
  tendsto_nhds_top_iff_nat.2 h

theorem tendsto_nat_nhds_top : Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞) :=
  tendsto_nhds_top fun n =>
    mem_atTop_sets.2 ⟨n + 1, fun _m hm => mem_setOf.2 <| Nat.cast_lt.2 <| Nat.lt_of_succ_le hm⟩

@[simp, norm_cast]
theorem tendsto_coe_nhds_top {f : α → ℝ≥0} {l : Filter α} :
    Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_nnreal, atTop_basis_Ioi.tendsto_right_iff]; simp

@[simp]
theorem tendsto_ofReal_nhds_top {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop :=
  tendsto_coe_nhds_top.trans Real.tendsto_toNNReal_atTop_iff

theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞) :=
  tendsto_ofReal_nhds_top.2 tendsto_id

theorem nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [pos_iff_ne_zero, Iio]

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis

theorem nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic

-- TODO: add a TC for `≠ ∞`?
@[instance]
theorem nhdsGT_coe_neBot {r : ℝ≥0} : (𝓝[>] (r : ℝ≥0∞)).NeBot :=
  nhdsGT_neBot_of_exists_gt ⟨∞, ENNReal.coe_lt_top⟩

@[instance] theorem nhdsGT_zero_neBot : (𝓝[>] (0 : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance] theorem nhdsGT_one_neBot : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance] theorem nhdsGT_nat_neBot (n : ℕ) : (𝓝[>] (n : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance]
theorem nhdsGT_ofNat_neBot (n : ℕ) [n.AtLeastTwo] : (𝓝[>] (OfNat.ofNat n : ℝ≥0∞)).NeBot :=
  nhdsGT_coe_neBot

@[instance]
theorem nhdsLT_neBot [NeZero x] : (𝓝[<] x).NeBot :=
  nhdsWithin_Iio_self_neBot' ⟨0, NeZero.pos x⟩

/-- Closed intervals `Set.Icc (x - ε) (x + ε)`, `ε ≠ 0`, form a basis of neighborhoods of an
extended nonnegative real number `x ≠ ∞`. We use `Set.Icc` instead of `Set.Ioo` because this way the
statement works for `x = 0`.
-/
theorem hasBasis_nhds_of_ne_top' (xt : x ≠ ∞) :
    (𝓝 x).HasBasis (· ≠ 0) (fun ε => Icc (x - ε) (x + ε)) := by
  rcases (zero_le x).eq_or_lt with rfl | x0
  · simp_rw [zero_tsub, zero_add, ← bot_eq_zero, Icc_bot, ← bot_lt_iff_ne_bot]
    exact nhds_bot_basis_Iic
  · refine (nhds_basis_Ioo' ⟨_, x0⟩ ⟨_, xt.lt_top⟩).to_hasBasis ?_ fun ε ε0 => ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rcases exists_between (tsub_pos_of_lt ha) with ⟨ε, ε0, hε⟩
      rcases lt_iff_exists_add_pos_lt.1 hb with ⟨δ, δ0, hδ⟩
      refine ⟨min ε δ, (lt_min ε0 (coe_pos.2 δ0)).ne', Icc_subset_Ioo ?_ ?_⟩
      · exact lt_tsub_comm.2 ((min_le_left _ _).trans_lt hε)
      · exact (add_le_add_left (min_le_right _ _) _).trans_lt hδ
    · exact ⟨(x - ε, x + ε), ⟨ENNReal.sub_lt_self xt x0.ne' ε0,
        lt_add_right xt ε0⟩, Ioo_subset_Icc_self⟩

theorem hasBasis_nhds_of_ne_top (xt : x ≠ ∞) :
    (𝓝 x).HasBasis (0 < ·) (fun ε => Icc (x - ε) (x + ε)) := by
  simpa only [pos_iff_ne_zero] using hasBasis_nhds_of_ne_top' xt

theorem Icc_mem_nhds (xt : x ≠ ∞) (ε0 : ε ≠ 0) : Icc (x - ε) (x + ε) ∈ 𝓝 x :=
  (hasBasis_nhds_of_ne_top' xt).mem_of_mem ε0

theorem nhds_of_ne_top (xt : x ≠ ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) :=
  (hasBasis_nhds_of_ne_top xt).eq_biInf

theorem biInf_le_nhds : ∀ x : ℝ≥0∞, ⨅ ε > 0, 𝓟 (Icc (x - ε) (x + ε)) ≤ 𝓝 x
  | ∞ => iInf₂_le_of_le 1 one_pos <| by
    simpa only [← coe_one, top_sub_coe, top_add, Icc_self, principal_singleton] using pure_le_nhds _
  | (x : ℝ≥0) => (nhds_of_ne_top coe_ne_top).ge

protected theorem tendsto_nhds_of_Icc {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (a - ε) (a + ε)) : Tendsto u f (𝓝 a) := by
  refine Tendsto.mono_right ?_ (biInf_le_nhds _)
  simpa only [tendsto_iInf, tendsto_principal]

/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (a - ε) (a + ε) := by
  simp only [nhds_of_ne_top ha, tendsto_iInf, tendsto_principal]

protected theorem tendsto_nhds_zero {f : Filter α} {u : α → ℝ≥0∞} :
    Tendsto u f (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ≤ ε :=
  nhds_zero_basis_Iic.tendsto_right_iff

theorem tendsto_const_sub_nhds_zero_iff {l : Filter α} {f : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n ↦ a - f n) l (𝓝 0) ↔ Tendsto (fun n ↦ f n) l (𝓝 a) := by
  rw [ENNReal.tendsto_nhds_zero, ENNReal.tendsto_nhds ha]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · filter_upwards [h ε hε] with n hn
    refine ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩
    rw [tsub_le_iff_right] at hn ⊢
    rwa [add_comm]
  · filter_upwards [h ε hε] with n hn
    have hN_left := hn.1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]

protected theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : a ≠ ∞) : Tendsto f atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Icc (a - ε) (a + ε) :=
  .trans (atTop_basis.tendsto_iff (hasBasis_nhds_of_ne_top ha)) (by simp only [true_and]; rfl)

protected theorem tendsto_atTop_zero [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} :
    Tendsto f atTop (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε :=
  .trans (atTop_basis.tendsto_iff nhds_zero_basis_Iic) (by simp only [true_and]; rfl)

theorem tendsto_atTop_zero_iff_le_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β → ℝ≥0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : β, f n ≤ ε := by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h ↦ fun ε hε ↦ ?_, fun h ↦ fun ε hε ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm ↦ (hf hm).trans hn⟩

theorem tendsto_atTop_zero_iff_lt_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β → ℝ≥0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : β, f n < ε := by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hf]
  constructor <;> intro h ε hε
  · obtain ⟨n, hn⟩ := h (min 1 (ε / 2))
      (lt_min_iff.mpr ⟨zero_lt_one, (ENNReal.div_pos_iff.mpr ⟨ne_of_gt hε, ENNReal.ofNat_ne_top⟩)⟩)
    · refine ⟨n, hn.trans_lt ?_⟩
      by_cases hε_top : ε = ∞
      · rw [hε_top]
        exact (min_le_left _ _).trans_lt ENNReal.one_lt_top
      refine (min_le_right _ _).trans_lt ?_
      rw [ENNReal.div_lt_iff (Or.inr hε.ne') (Or.inr hε_top)]
      conv_lhs => rw [← mul_one ε]
      rw [ENNReal.mul_lt_mul_left hε.ne' hε_top]
      norm_num
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn.le⟩

theorem tendsto_sub : ∀ {a b : ℝ≥0∞}, (a ≠ ∞ ∨ b ≠ ∞) →
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) (𝓝 (a, b)) (𝓝 (a - b))
  | ∞, ∞, h => by simp only [ne_eq, not_true_eq_false, or_self] at h
  | ∞, (b : ℝ≥0), _ => by
    rw [top_sub_coe, tendsto_nhds_top_iff_nnreal]
    refine fun x => ((lt_mem_nhds <| @coe_lt_top (b + 1 + x)).prod_nhds
      (ge_mem_nhds <| coe_lt_coe.2 <| lt_add_one b)).mono fun y hy => ?_
    rw [lt_tsub_iff_left]
    calc y.2 + x ≤ ↑(b + 1) + x := add_le_add_right hy.2 _
    _ < y.1 := hy.1
  | (a : ℝ≥0), ∞, _ => by
    rw [sub_top]
    refine (tendsto_pure.2 ?_).mono_right (pure_le_nhds _)
    exact ((gt_mem_nhds <| coe_lt_coe.2 <| lt_add_one a).prod_nhds
      (lt_mem_nhds <| @coe_lt_top (a + 1))).mono fun x hx =>
        tsub_eq_zero_iff_le.2 (hx.1.trans hx.2).le
  | (a : ℝ≥0), (b : ℝ≥0), _ => by
    simp only [nhds_coe_coe, tendsto_map'_iff, ← ENNReal.coe_sub, Function.comp_def, tendsto_coe]
    exact continuous_sub.tendsto (a, b)

protected theorem Tendsto.sub {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun a => ma a - mb a) f (𝓝 (a - b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 - p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a - b)) from
    Tendsto.comp (ENNReal.tendsto_sub h) (hma.prodMk_nhds hmb)

protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ∞) (hb : b ≠ 0 ∨ a ≠ ∞) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) := by
  have ht : ∀ b : ℝ≥0∞, b ≠ 0 →
      Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (∞, b)) (𝓝 ∞) := fun b hb => by
    refine tendsto_nhds_top_iff_nnreal.2 fun n => ?_
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have : ∀ᶠ c : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (∞, b), ↑n / ↑ε < c.1 ∧ ↑ε < c.2 :=
      (lt_mem_nhds <| div_lt_top coe_ne_top hε.ne').prod_nhds (lt_mem_nhds hεb)
    refine this.mono fun c hc => ?_
    exact (ENNReal.div_mul_cancel hε.ne' coe_ne_top).symm.trans_lt (mul_lt_mul hc.1 hc.2)
  induction a with
  | top => simp only [ne_eq, or_false, not_true_eq_false] at hb; simp [ht b hb, top_mul hb]
  | coe a =>
    induction b with
    | top =>
      simp only [ne_eq, or_false, not_true_eq_false] at ha
      simpa [Function.comp_def, mul_comm, mul_top ha]
        using (ht a ha).comp (continuous_swap.tendsto (ofNNReal a, ∞))
    | coe b =>
      simp only [nhds_coe_coe, ← coe_mul, tendsto_coe, tendsto_map'_iff, Function.comp_def,
        tendsto_mul]

protected theorem Tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ∞) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ 0 ∨ a ≠ ∞) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prodMk_nhds hmb)

theorem _root_.ContinuousOn.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : ∀ x ∈ s, f x ≠ 0 ∨ g x ≠ ∞)
    (h₂ : ∀ x ∈ s, g x ≠ 0 ∨ f x ≠ ∞) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)

theorem _root_.Continuous.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : ∀ x, f x ≠ 0 ∨ g x ≠ ∞) (h₂ : ∀ x, g x ≠ 0 ∨ f x ≠ ∞) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)

protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ∞) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a ≠ 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb

protected theorem Tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ∞) : Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha

theorem tendsto_finset_prod_of_ne_top {ι : Type*} {f : ι → α → ℝ≥0∞} {x : Filter α} {a : ι → ℝ≥0∞}
    (s : Finset ι) (h : ∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) (h' : ∀ i ∈ s, a i ≠ ∞) :
    Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [tendsto_const_nhds]
  | insert _ _ has IH =>
    simp only [Finset.prod_insert has]
    apply Tendsto.mul (h _ (Finset.mem_insert_self _ _))
    · right
      exact prod_ne_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)
    · exact IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi =>
        h' _ (Finset.mem_insert_of_mem hi)
    · exact Or.inr (h' _ (Finset.mem_insert_self _ _))

protected theorem continuousAt_const_mul {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (a * ·) b :=
  Tendsto.const_mul tendsto_id h.symm

protected theorem continuousAt_mul_const {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (fun x => x * a) b :=
  Tendsto.mul_const tendsto_id h.symm

@[fun_prop]
protected theorem continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ∞) : Continuous (a * ·) :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_const_mul (Or.inl ha)

@[fun_prop]
protected theorem continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ∞) : Continuous fun x => x * a :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_mul_const (Or.inl ha)

@[fun_prop]
protected theorem continuous_div_const (c : ℝ≥0∞) (c_ne_zero : c ≠ 0) :
    Continuous fun x : ℝ≥0∞ => x / c :=
  ENNReal.continuous_mul_const <| ENNReal.inv_ne_top.2 c_ne_zero

@[continuity, fun_prop]
protected theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n := by
  induction n with
  | zero => simp [continuous_const]
  | succ n IH =>
    simp_rw [pow_add, pow_one, continuous_iff_continuousAt]
    intro x
    refine ENNReal.Tendsto.mul (IH.tendsto _) ?_ tendsto_id ?_ <;> by_cases H : x = 0
    · simp only [H, zero_ne_top, Ne, or_true, not_false_iff]
    · exact Or.inl fun h => H (pow_eq_zero h)
    · simp only [H, pow_eq_top_iff, zero_ne_top, false_or, not_true, Ne,
        not_false_iff, false_and]
    · simp only [H, true_or, Ne, not_false_iff]

theorem continuousOn_sub :
    ContinuousOn (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) { p : ℝ≥0∞ × ℝ≥0∞ | p ≠ ⟨∞, ∞⟩ } := by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne, Set.mem_setOf_eq, Prod.mk_inj] at hp
  exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_sub (not_and_or.mp hp))

theorem continuous_sub_left {a : ℝ≥0∞} (a_ne_top : a ≠ ∞) : Continuous (a - ·) := by
  change Continuous (Function.uncurry Sub.sub ∘ (a, ·))
  refine continuousOn_sub.comp_continuous (.prodMk_right a) fun x => ?_
  simp only [a_ne_top, Ne, mem_setOf_eq, Prod.mk_inj, false_and, not_false_iff]

theorem continuous_nnreal_sub {a : ℝ≥0} : Continuous fun x : ℝ≥0∞ => (a : ℝ≥0∞) - x :=
  continuous_sub_left coe_ne_top

theorem continuousOn_sub_left (a : ℝ≥0∞) : ContinuousOn (a - ·) { x : ℝ≥0∞ | x ≠ ∞ } := by
  rw [show (fun x => a - x) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨a, x⟩ by rfl]
  apply continuousOn_sub.comp (by fun_prop)
  rintro _ h (_ | _)
  exact h none_eq_top

theorem continuous_sub_right (a : ℝ≥0∞) : Continuous fun x : ℝ≥0∞ => x - a := by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const, tsub_eq_zero_of_le]
  · rw [show (fun x => x - a) = (fun p : ℝ≥0∞ × ℝ≥0∞ => p.fst - p.snd) ∘ fun x => ⟨x, a⟩ by rfl]
    apply continuousOn_sub.comp_continuous (by fun_prop)
    intro x
    simp only [a_infty, Ne, mem_setOf_eq, Prod.mk_inj, and_false, not_false_iff]

protected theorem Tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((ENNReal.continuous_pow n).tendsto a).comp hm

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0∞} (h : ∀ a < 1, a * x ≤ y) : x ≤ y := by
  have : Tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| Eventually.of_forall h)

theorem inv_limsup {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.limsup_apply

theorem inv_liminf {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.liminf_apply

@[fun_prop]
protected theorem continuous_zpow : ∀ n : ℤ, Continuous (· ^ n : ℝ≥0∞ → ℝ≥0∞)
  | (n : ℕ) => mod_cast ENNReal.continuous_pow n
  | .negSucc n => by simpa using (ENNReal.continuous_pow _).inv

@[simp] -- TODO: generalize to `[InvolutiveInv _] [ContinuousInv _]`
protected theorem tendsto_inv_iff {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun x => (m x)⁻¹) f (𝓝 a⁻¹) ↔ Tendsto m f (𝓝 a) :=
  ⟨fun h => by simpa only [inv_inv] using Tendsto.inv h, Tendsto.inv⟩

protected theorem Tendsto.div {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ ∞ ∨ a ≠ ∞) : Tendsto (fun a => ma a / mb a) f (𝓝 (a / b)) := by
  apply Tendsto.mul hma _ (ENNReal.tendsto_inv_iff.2 hmb) _ <;> simp [ha, hb]

protected theorem Tendsto.const_div {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ ∞ ∨ a ≠ ∞) : Tendsto (fun b => a / m b) f (𝓝 (a / b)) := by
  apply Tendsto.const_mul (ENNReal.tendsto_inv_iff.2 hm)
  simp [hb]

protected theorem Tendsto.div_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) : Tendsto (fun x => m x / b) f (𝓝 (a / b)) := by
  apply Tendsto.mul_const hm
  simp [ha]

protected theorem tendsto_inv_nat_nhds_zero : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
  ENNReal.inv_top ▸ ENNReal.tendsto_inv_iff.2 tendsto_nat_nhds_top

protected theorem tendsto_coe_sub {b : ℝ≥0∞} :
    Tendsto (fun b : ℝ≥0∞ => ↑r - b) (𝓝 b) (𝓝 (↑r - b)) :=
  continuous_nnreal_sub.tendsto _

theorem exists_countable_dense_no_zero_top :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s := by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s :=
    exists_countable_dense_no_bot_top ℝ≥0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩

end TopologicalSpace

section Liminf

theorem exists_frequently_lt_of_liminf_ne_top {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (Real.nnabs (x n) : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, x n < R := by
  by_contra h
  simp_rw [not_exists, not_frequently, not_lt] at h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r] with i hi using hi.trans (le_abs_self (x i))

theorem exists_frequently_lt_of_liminf_ne_top' {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (Real.nnabs (x n) : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, R < x n := by
  by_contra h
  simp_rw [not_exists, not_frequently, not_lt] at h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)] with i hi using(le_neg.1 hi).trans (neg_le_abs _)

theorem exists_upcrossings_of_not_bounded_under {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hf : liminf (fun i => (Real.nnabs (x i) : ℝ≥0∞)) l ≠ ∞)
    (hbdd : ¬IsBoundedUnder (· ≤ ·) l fun i => |x i|) :
    ∃ a b : ℚ, a < b ∧ (∃ᶠ i in l, x i < a) ∧ ∃ᶠ i in l, ↑b < x i := by
  rw [isBoundedUnder_le_abs, not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, ?_, ?_⟩
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 (lt_of_lt_of_le hq (not_lt.1 hx)).le
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q + 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf
    obtain ⟨q, hq⟩ := exists_rat_lt R
    refine ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, ?_, ?_⟩
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q - 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 ((not_lt.1 hx).trans hq.le)

end Liminf

section tsum

variable {f g : α → ℝ≥0∞}

@[norm_cast]
protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
    HasSum (fun a => (f a : ℝ≥0∞)) ↑r ↔ HasSum f r := by
  simp only [HasSum, ← coe_finset_sum, tendsto_coe]

protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : ℝ≥0∞)) = r :=
  (ENNReal.hasSum_coe.2 h).tsum_eq

protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : ℝ≥0∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

@[simp]
protected theorem summable : Summable f :=
  ⟨_, ENNReal.hasSum⟩

macro_rules | `(tactic| gcongr_discharger) => `(tactic| apply ENNReal.summable)

theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : ℝ≥0∞)) ≠ ∞ ↔ Summable f := by
  refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
  lift ∑' b, (f b : ℝ≥0∞) to ℝ≥0 using h with a ha
  refine ⟨a, ENNReal.hasSum_coe.1 ?_⟩
  rw [ha]
  exact ENNReal.summable.hasSum

protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a :=
  ENNReal.hasSum.tsum_eq

protected theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
    ∑' a, f a = ⨆ i, ∑ a ∈ s i, f a := by
  rw [ENNReal.tsum_eq_iSup_sum]
  symm
  change ⨆ i : ι, (fun t : Finset α => ∑ a ∈ t, f a) (s i) = ⨆ s : Finset α, ∑ a ∈ s, f a
  exact (Finset.sum_mono_set f).iSup_comp_eq hs

protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → ℝ≥0∞) :
    ∑' p : Σ a, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℝ≥0∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  ENNReal.summable.tsum_sigma' fun _ => ENNReal.summable

protected theorem tsum_biUnion' {ι : Type*} {S : Set ι} {f : α → ENNReal} {t : ι → Set α}
    (h : S.PairwiseDisjoint t) : ∑' x : ⋃ i ∈ S, t i, f x = ∑' (i : S), ∑' (x : t i), f x := by
  simp [← ENNReal.tsum_sigma, ← (Set.biUnionEqSigmaOfDisjoint h).tsum_eq]

protected theorem tsum_biUnion {ι : Type*} {f : α → ENNReal} {t : ι → Set α}
    (h : Set.univ.PairwiseDisjoint t) : ∑' x : ⋃ i, t i, f x = ∑' (i) (x : t i), f x := by
  nth_rw 2 [← tsum_univ]
  rw [← ENNReal.tsum_biUnion' h, Set.biUnion_univ]

protected theorem tsum_prod {f : α → β → ℝ≥0∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

protected theorem tsum_prod' {f : α × β → ℝ≥0∞} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
  ENNReal.summable.tsum_prod' fun _ => ENNReal.summable

protected theorem tsum_comm {f : α → β → ℝ≥0∞} : ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b :=
  ENNReal.summable.tsum_comm' (fun _ => ENNReal.summable) fun _ => ENNReal.summable

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  ENNReal.summable.tsum_add ENNReal.summable

protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : ∑' a, f a ≤ ∑' a, g a :=
  ENNReal.summable.tsum_le_tsum h ENNReal.summable

protected theorem sum_le_tsum {f : α → ℝ≥0∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  ENNReal.summable.sum_le_tsum s (fun _ _ => zero_le _)

protected theorem tsum_eq_iSup_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a ∈ Finset.range (N i), f a :=
  ENNReal.tsum_eq_iSup_sum' _ fun t =>
    let ⟨n, hn⟩ := t.exists_nat_subset_range
    let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
    ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

protected theorem tsum_eq_iSup_nat {f : ℕ → ℝ≥0∞} :
    ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a ∈ Finset.range i, f a :=
  ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range

protected theorem tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
    ∑' i, f i = liminf (fun n => ∑ i ∈ Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm

protected theorem tsum_eq_limsup_sum_nat {f : ℕ → ℝ≥0∞} :
    ∑' i, f i = limsup (fun n => ∑ i ∈ Finset.range n, f i) atTop :=
  ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  ENNReal.summable.le_tsum' a

@[simp]
protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  ENNReal.summable.tsum_eq_zero_iff

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a

protected theorem lt_top_of_tsum_ne_top {a : α → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞) (j : α) :
    a j < ∞ := by
  contrapose! tsum_ne_top with h
  exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

@[simp]
protected theorem tsum_top [Nonempty α] : ∑' _ : α, ∞ = ∞ :=
  let ⟨a⟩ := ‹Nonempty α›
  ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

theorem tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : ℝ≥0∞} (hc : c ≠ 0) :
    ∑' _ : α, c = ∞ := by
  have A : Tendsto (fun n : ℕ => (n : ℝ≥0∞) * c) atTop (𝓝 (∞ * c)) := by
    apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
    simp only [true_or, top_ne_zero, Ne, not_false_iff]
  have B : ∀ n : ℕ, (n : ℝ≥0∞) * c ≤ ∑' _ : α, c := fun n => by
    rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
    simpa [hs] using @ENNReal.sum_le_tsum α (fun _ => c) s
  simpa [hc] using le_of_tendsto' A B

protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
  h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩

protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  · rw [← ENNReal.tsum_eq_zero] at hf
    have : Tendsto (fun s : Finset α => ∑ j ∈ s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
      simp only [← Finset.mul_sum]
      exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
    exact HasSum.tsum_eq this

protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
  simp [mul_comm, ENNReal.tsum_mul_left]

protected theorem tsum_const_smul {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (a : R) :
    ∑' i, a • f i = a • ∑' i, f i := by
  simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : ℝ≥0∞)) _

@[simp]
theorem tsum_iSup_eq {α : Type*} (a : α) {f : α → ℝ≥0∞} : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
  (tsum_eq_single a fun _ h => by simp [h.symm]).trans <| by simp

theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  refine ⟨HasSum.tendsto_sum_nat, fun h => ?_⟩
  rw [← iSup_eq_of_tendsto _ h, ← ENNReal.tsum_eq_iSup_nat]
  · exact ENNReal.summable.hasSum
  · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hst)

theorem tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
  rw [← hasSum_iff_tendsto_nat]
  exact ENNReal.summable.hasSum

theorem toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) (x : α) :
    (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
  coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _

theorem summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) :
    Summable (ENNReal.toNNReal ∘ f) := by
  simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto f cofinite (𝓝 0) := by
  have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
  have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
    funext fun n => (coe_toNNReal (f_ne_top n)).symm
  rw [h_f_coe, ← @coe_zero, tendsto_coe]
  exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)

theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto f atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_cofinite_zero_of_tsum_ne_top hf

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' x, f x ≠ ∞) :
    Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  convert ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
  rw [ENNReal.coe_tsum]
  exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

protected theorem tsum_apply {ι α : Type*} {f : ι → α → ℝ≥0∞} {x : α} :
    (∑' i, f i) x = ∑' i, f i x :=
  tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable

theorem tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
    ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
  have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
  ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]

theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℝ≥0∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  ENNReal.summable.tsum_le_tsum_of_inj f hf (fun _ _ => zero_le _) (fun _ => le_rfl)
    ENNReal.summable

theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℝ≥0∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
  _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

theorem tsum_mono_subtype (f : α → ℝ≥0∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  tsum_comp_le_tsum_of_injective (inclusion_injective h) _

theorem tsum_iUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

theorem tsum_biUnion_le_tsum {ι : Type*} (f : α → ℝ≥0∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_set_coe _ <| by simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

theorem tsum_biUnion_le {ι : Type*} (f : α → ℝ≥0∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (tsum_biUnion_le_tsum f s.toSet t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

theorem tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α → ℝ≥0∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype]
  exact tsum_iUnion_le_tsum f t

theorem tsum_union_le (f : α → ℝ≥0∞) (s t : Set α) :
    ∑' x : ↑(s ∪ t), f x ≤ ∑' x : s, f x + ∑' x : t, f x :=
  calc ∑' x : ↑(s ∪ t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_set_coe _ union_eq_iUnion
  _ ≤ _ := by simpa using tsum_iUnion_le f (cond · s t)

open Classical in
theorem tsum_eq_add_tsum_ite {f : β → ℝ≥0∞} (b : β) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  ENNReal.summable.tsum_eq_add_tsum_ite' b

theorem tsum_add_one_eq_top {f : ℕ → ℝ≥0∞} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
    ∑' n, f (n + 1) = ∞ := by
  rw [tsum_eq_zero_add' ENNReal.summable, add_eq_top] at hf
  exact hf.resolve_left hf0

/-- A sum of extended nonnegative reals which is finite can have only finitely many terms
above any positive threshold. -/
theorem finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι → ℝ≥0∞} (tsum_ne_top : ∑' i, a i ≠ ∞)
    {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite := by
  by_contra h
  have := Infinite.to_subtype h
  refine tsum_ne_top (top_unique ?_)
  calc ∞ = ∑' _ : { i | ε ≤ a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
  _ ≤ ∑' i, a i := ENNReal.summable.tsum_le_tsum_of_inj (↑)
    Subtype.val_injective (fun _ _ => zero_le _) (fun i => i.2) ENNReal.summable

/-- Markov's inequality for `Finset.card` and `tsum` in `ℝ≥0∞`. -/
theorem finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι → ℝ≥0∞} {c : ℝ≥0∞} (c_ne_top : c ≠ ∞)
    (tsum_le_c : ∑' i, a i ≤ c) {ε : ℝ≥0∞} (ε_ne_zero : ε ≠ 0) :
    ∃ hf : { i : ι | ε ≤ a i }.Finite, #hf.toFinset ≤ c / ε := by
  have hf : { i : ι | ε ≤ a i }.Finite :=
    finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
  refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
  calc #hf.toFinset * ε = ∑ _i ∈ hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ hf.toFinset, a i := Finset.sum_le_sum fun i => hf.mem_toFinset.1
    _ ≤ ∑' i, a i := ENNReal.sum_le_tsum _
    _ ≤ c := tsum_le_c

theorem tsum_fiberwise (f : β → ℝ≥0∞) (g : β → γ) :
    ∑' x, ∑' b : g ⁻¹' {x}, f b = ∑' i, f i := by
  apply HasSum.tsum_eq
  let equiv := Equiv.sigmaFiberEquiv g
  apply (equiv.hasSum_iff.mpr ENNReal.summable.hasSum).sigma
  exact fun _ ↦ ENNReal.summable.hasSum_iff.mpr rfl

end tsum

theorem tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  lift f to ι → ℝ≥0 using hf
  lift x to ℝ≥0 using hx
  simp [tendsto_coe]

theorem tsum_coe_ne_top_iff_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) ≠ ∞ ↔ Summable fun a => (f a : ℝ) := by
  rw [NNReal.summable_coe]
  exact tsum_coe_ne_top_iff_summable

theorem tsum_coe_eq_top_iff_not_summable_coe {f : α → ℝ≥0} :
    (∑' a, (f a : ℝ≥0∞)) = ∞ ↔ ¬Summable fun a => (f a : ℝ) :=
  tsum_coe_ne_top_iff_summable_coe.not_right

theorem hasSum_toReal {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) :
    HasSum (fun x => (f x).toReal) (∑' x, (f x).toReal) := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hsum
  simp only [coe_toReal, ← NNReal.coe_tsum, NNReal.hasSum_coe]
  exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum

theorem summable_toReal {f : α → ℝ≥0∞} (hsum : ∑' x, f x ≠ ∞) : Summable fun x => (f x).toReal :=
  (hasSum_toReal hsum).summable

end ENNReal

namespace NNReal

theorem tsum_eq_toNNReal_tsum {f : β → ℝ≥0} : ∑' b, f b = (∑' b, (f b : ℝ≥0∞)).toNNReal := by
  by_cases h : Summable f
  · rw [← ENNReal.coe_tsum h, ENNReal.toNNReal_coe]
  · have A := tsum_eq_zero_of_not_summable h
    simp only [← ENNReal.tsum_coe_ne_top_iff_summable, Classical.not_not] at h
    simp only [h, ENNReal.toNNReal_top, A]

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem exists_le_hasSum_of_le {f g : β → ℝ≥0} {r : ℝ≥0} (hgf : ∀ b, g b ≤ f b) (hfr : HasSum f r) :
    ∃ p ≤ r, HasSum g p :=
  have : (∑' b, (g b : ℝ≥0∞)) ≤ r := by
    refine hasSum_le (fun b => ?_) ENNReal.summable.hasSum (ENNReal.hasSum_coe.2 hfr)
    exact ENNReal.coe_le_coe.2 (hgf _)
  let ⟨p, Eq, hpr⟩ := ENNReal.le_coe_iff.1 this
  ⟨p, hpr, ENNReal.hasSum_coe.1 <| Eq ▸ ENNReal.summable.hasSum⟩

/-- Comparison test of convergence of `ℝ≥0`-valued series. -/
theorem summable_of_le {f g : β → ℝ≥0} (hgf : ∀ b, g b ≤ f b) : Summable f → Summable g
  | ⟨_r, hfr⟩ =>
    let ⟨_p, _, hp⟩ := exists_le_hasSum_of_le hgf hfr
    hp.summable

/-- Summable non-negative functions have countable support -/
theorem _root_.Summable.countable_support_nnreal (f : α → ℝ≥0) (h : Summable f) :
    f.support.Countable := by
  rw [← NNReal.summable_coe] at h
  simpa [support] using h.countable_support

/-- A series of non-negative real numbers converges to `r` in the sense of `HasSum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat {f : ℕ → ℝ≥0} {r : ℝ≥0} :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  rw [← ENNReal.hasSum_coe, ENNReal.hasSum_iff_tendsto_nat]
  simp only [← ENNReal.coe_finset_sum]
  exact ENNReal.tendsto_coe

theorem not_summable_iff_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    ¬Summable f ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  constructor
  · intro h
    refine ((tendsto_of_monotone ?_).resolve_right h).comp ?_
    exacts [Finset.sum_mono_set _, tendsto_finset_range]
  · rintro hnat ⟨r, hr⟩
    exact not_tendsto_nhds_of_tendsto_atTop hnat _ (hasSum_iff_tendsto_nat.1 hr)

theorem summable_iff_not_tendsto_nat_atTop {f : ℕ → ℝ≥0} :
    Summable f ↔ ¬Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop atTop := by
  rw [← not_iff_not, Classical.not_not, not_summable_iff_tendsto_nat_atTop]

theorem summable_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f := by
  refine summable_iff_not_tendsto_nat_atTop.2 fun H => ?_
  rcases exists_lt_of_tendsto_atTop H 0 c with ⟨n, -, hn⟩
  exact lt_irrefl _ (hn.trans_le (h n))

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0} {c : ℝ≥0}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  (summable_of_sum_range_le h).tsum_le_of_sum_range_le h

theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ≥0} (hf : Summable f) {i : β → α}
    (hi : Function.Injective i) : (∑' x, f (i x)) ≤ ∑' x, f x :=
  (summable_comp_injective hf hi).tsum_le_tsum_of_inj i hi (fun _ _ => zero_le _) (fun _ => le_rfl)
    hf

theorem summable_sigma {β : α → Type*} {f : (Σ x, β x) → ℝ≥0} :
    Summable f ↔ (∀ x, Summable fun y => f ⟨x, y⟩) ∧ Summable fun x => ∑' y, f ⟨x, y⟩ := by
  constructor
  · simp only [← NNReal.summable_coe, NNReal.coe_tsum]
    exact fun h => ⟨h.sigma_factor, h.sigma⟩
  · rintro ⟨h₁, h₂⟩
    simpa only [← ENNReal.tsum_coe_ne_top_iff_summable, ENNReal.tsum_sigma',
      ENNReal.coe_tsum (h₁ _)] using h₂

theorem indicator_summable {f : α → ℝ≥0} (hf : Summable f) (s : Set α) :
    Summable (s.indicator f) := by
  classical
  refine NNReal.summable_of_le (fun a => le_trans (le_of_eq (s.indicator_apply f a)) ?_) hf
  split_ifs
  · exact le_refl (f a)
  · exact zero_le_coe

theorem tsum_indicator_ne_zero {f : α → ℝ≥0} (hf : Summable f) {s : Set α} (h : ∃ a ∈ s, f a ≠ 0) :
    (∑' x, (s.indicator f) x) ≠ 0 := fun h' =>
  let ⟨a, ha, hap⟩ := h
  hap ((Set.indicator_apply_eq_self.mpr (absurd ha)).symm.trans
    ((indicator_summable hf s).tsum_eq_zero_iff.1 h' a))

open Finset

/-- For `f : ℕ → ℝ≥0`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0) : Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  rw [← tendsto_coe]
  convert _root_.tendsto_sum_nat_add fun i => (f i : ℝ)
  norm_cast

nonrec theorem hasSum_lt {f g : α → ℝ≥0} {sf sg : ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  have A : ∀ a : α, (f a : ℝ) ≤ g a := fun a => NNReal.coe_le_coe.2 (h a)
  have : (sf : ℝ) < sg := hasSum_lt A (NNReal.coe_lt_coe.2 hi) (hasSum_coe.2 hf) (hasSum_coe.2 hg)
  exact NNReal.coe_lt_coe.1 this

@[mono]
theorem hasSum_strict_mono {f g : α → ℝ≥0} {sf sg : ℝ≥0} (hf : HasSum f sf) (hg : HasSum g sg)
    (h : f < g) : sf < sg :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  hasSum_lt hle hi hf hg

theorem tsum_lt_tsum {f g : α → ℝ≥0} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hg : Summable g) : ∑' n, f n < ∑' n, g n :=
  hasSum_lt h hi (summable_of_le h hg).hasSum hg.hasSum

@[mono]
theorem tsum_strict_mono {f g : α → ℝ≥0} (hg : Summable g) (h : f < g) : ∑' n, f n < ∑' n, g n :=
  let ⟨hle, _i, hi⟩ := Pi.lt_def.mp h
  tsum_lt_tsum hle hi hg

theorem tsum_pos {g : α → ℝ≥0} (hg : Summable g) (i : α) (hi : 0 < g i) : 0 < ∑' b, g b := by
  rw [← tsum_zero]
  exact tsum_lt_tsum (fun a => zero_le _) hi hg

open Classical in
theorem tsum_eq_add_tsum_ite {f : α → ℝ≥0} (hf : Summable f) (i : α) :
    ∑' x, f x = f i + ∑' x, ite (x = i) 0 (f x) := by
  refine (NNReal.summable_of_le (fun i' => ?_) hf).tsum_eq_add_tsum_ite' i
  rw [Function.update_apply]
  split_ifs <;> simp only [zero_le', le_rfl]

end NNReal

namespace ENNReal

theorem tsum_toNNReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toNNReal = ∑' a, (f a).toNNReal :=
  (congr_arg ENNReal.toNNReal (tsum_congr fun x => (coe_toNNReal (hf x)).symm)).trans
    NNReal.tsum_eq_toNNReal_tsum.symm

theorem tsum_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ∞) :
    (∑' a, f a).toReal = ∑' a, (f a).toReal := by
  simp only [ENNReal.toReal, tsum_toNNReal_eq hf, NNReal.coe_tsum]

theorem tendsto_sum_nat_add (f : ℕ → ℝ≥0∞) (hf : ∑' i, f i ≠ ∞) :
    Tendsto (fun i => ∑' k, f (k + i)) atTop (𝓝 0) := by
  lift f to ℕ → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
  replace hf : Summable f := tsum_coe_ne_top_iff_summable.1 hf
  simp only [← ENNReal.coe_tsum, NNReal.summable_nat_add _ hf, ← ENNReal.coe_zero]
  exact mod_cast NNReal.tendsto_sum_nat_add f

theorem tsum_le_of_sum_range_le {f : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c :=
  ENNReal.summable.tsum_le_of_sum_range_le h

theorem hasSum_lt {f g : α → ℝ≥0∞} {sf sg : ℝ≥0∞} {i : α} (h : ∀ a : α, f a ≤ g a) (hi : f i < g i)
    (hsf : sf ≠ ∞) (hf : HasSum f sf) (hg : HasSum g sg) : sf < sg := by
  by_cases hsg : sg = ∞
  · exact hsg.symm ▸ lt_of_le_of_ne le_top hsf
  · have hg' : ∀ x, g x ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top (hg.tsum_eq.symm ▸ hsg)
    lift f to α → ℝ≥0 using fun x =>
      ne_of_lt (lt_of_le_of_lt (h x) <| lt_of_le_of_ne le_top (hg' x))
    lift g to α → ℝ≥0 using hg'
    lift sf to ℝ≥0 using hsf
    lift sg to ℝ≥0 using hsg
    simp only [coe_le_coe, coe_lt_coe] at h hi ⊢
    exact NNReal.hasSum_lt h hi (ENNReal.hasSum_coe.1 hf) (ENNReal.hasSum_coe.1 hg)

theorem tsum_lt_tsum {f g : α → ℝ≥0∞} {i : α} (hfi : tsum f ≠ ∞) (h : ∀ a : α, f a ≤ g a)
    (hi : f i < g i) : ∑' x, f x < ∑' x, g x :=
  hasSum_lt h hi hfi ENNReal.summable.hasSum ENNReal.summable.hasSum

end ENNReal

theorem tsum_comp_le_tsum_of_inj {β : Type*} {f : α → ℝ} (hf : Summable f) (hn : ∀ a, 0 ≤ f a)
    {i : β → α} (hi : Function.Injective i) : tsum (f ∘ i) ≤ tsum f := by
  lift f to α → ℝ≥0 using hn
  rw [NNReal.summable_coe] at hf
  simpa only [Function.comp_def, ← NNReal.coe_tsum] using NNReal.tsum_comp_le_tsum_of_inj hf hi

/-- Comparison test of convergence of series of non-negative real numbers. -/
theorem Summable.of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
    (hf : Summable f) : Summable g := by
  lift f to β → ℝ≥0 using fun b => (hg b).trans (hgf b)
  lift g to β → ℝ≥0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf

theorem Summable.toNNReal {f : α → ℝ} (hf : Summable f) : Summable fun n => (f n).toNNReal := by
  apply NNReal.summable_coe.1
  refine .of_nonneg_of_le (fun n => NNReal.coe_nonneg _) (fun n => ?_) hf.abs
  simp only [le_abs_self, Real.coe_toNNReal', max_le_iff, abs_nonneg, and_self_iff]

lemma Summable.tsum_ofReal_lt_top {f : α → ℝ} (hf : Summable f) : ∑' i, .ofReal (f i) < ∞ := by
  unfold ENNReal.ofReal
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable]
  exact hf.toNNReal

lemma Summable.tsum_ofReal_ne_top {f : α → ℝ} (hf : Summable f) : ∑' i, .ofReal (f i) ≠ ∞ :=
  hf.tsum_ofReal_lt_top.ne

/-- Finitely summable non-negative functions have countable support -/
theorem _root_.Summable.countable_support_ennreal {f : α → ℝ≥0∞} (h : ∑' (i : α), f i ≠ ∞) :
    f.support.Countable := by
  lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top h
  simpa [support] using (ENNReal.tsum_coe_ne_top_iff_summable.1 h).countable_support_nnreal

/-- A series of non-negative real numbers converges to `r` in the sense of `HasSum` if and only if
the sequence of partial sum converges to `r`. -/
theorem hasSum_iff_tendsto_nat_of_nonneg {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
    HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) := by
  lift f to ℕ → ℝ≥0 using hf
  simp only [HasSum, ← NNReal.coe_sum, NNReal.tendsto_coe']
  exact exists_congr fun hr => NNReal.hasSum_iff_tendsto_nat

theorem ENNReal.ofReal_tsum_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ENNReal.ofReal (∑' n, f n) = ∑' n, ENNReal.ofReal (f n) := by
  simp_rw [ENNReal.ofReal, ENNReal.tsum_coe_eq (NNReal.hasSum_real_toNNReal_of_nonneg hf_nonneg hf)]

section

variable [EMetricSpace β]

open ENNReal Filter EMetric

/-- In an emetric ball, the distance between points is everywhere finite -/
theorem edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : ball a r) : edist x.1 y.1 ≠ ∞ :=
  ne_of_lt <|
    calc
      edist x y ≤ edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y]; exact ENNReal.add_lt_add x.2 y.2
      _ ≤ ∞ := le_top

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
def metricSpaceEMetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (ball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball

theorem nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ ball a r) :
    𝓝 x = map ((↑) : ball a r → β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq_nhds _ <| IsOpen.mem_nhds EMetric.isOpen_ball h).symm

end

section

variable [PseudoEMetricSpace α]

open EMetric

theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β → α} {y : α} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0) := by
  simp only [EMetric.nhds_basis_eball.tendsto_right_iff, EMetric.mem_ball,
    @tendsto_order ℝ≥0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and]

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem EMetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β → α} :
    CauchySeq s ↔ ∃ b : β → ℝ≥0∞, (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N) ∧
      Tendsto b atTop (𝓝 0) := EMetric.cauchySeq_iff.trans <| by
  constructor
  · intro hs
    /- `s` is Cauchy sequence. Let `b n` be the diameter of the set `s '' Set.Ici n`. -/
    refine ⟨fun N => EMetric.diam (s '' Ici N), fun n m N hn hm => ?_, ?_⟩
    -- Prove that it bounds the distances of points in the Cauchy sequence
    · exact EMetric.edist_le_diam_of_mem (mem_image_of_mem _ hn) (mem_image_of_mem _ hm)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    · refine ENNReal.tendsto_nhds_zero.2 fun ε ε0 => ?_
      rcases hs ε ε0 with ⟨N, hN⟩
      refine (eventually_ge_atTop N).mono fun n hn => EMetric.diam_le ?_
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      exact (hN _ (hn.trans hk) _ (hn.trans hl)).le
  · rintro ⟨b, ⟨b_bound, b_lim⟩⟩ ε εpos
    have : ∀ᶠ n in atTop, b n < ε := b_lim.eventually (gt_mem_nhds εpos)
    rcases this.exists with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    calc edist (s m) (s n) ≤ b N := b_bound m n N hm hn
    _ < ε := hN

theorem continuous_of_le_add_edist {f : α → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ x y, f x ≤ f y + C * edist x y) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ENNReal.tendsto_nhds_of_Icc fun ε ε0 => ?_
  rcases ENNReal.exists_nnreal_pos_mul_lt hC ε0.ne' with ⟨δ, δ0, hδ⟩
  rw [mul_comm] at hδ
  filter_upwards [EMetric.closedBall_mem_nhds x (ENNReal.coe_pos.2 δ0)] with y hy
  refine ⟨tsub_le_iff_right.2 <| (h x y).trans ?_, (h y x).trans ?_⟩ <;>
    refine add_le_add_left (le_trans (mul_le_mul_left' ?_ _) hδ.le) _
  exacts [EMetric.mem_closedBall'.1 hy, EMetric.mem_closedBall.1 hy]

theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 := by
  apply continuous_of_le_add_edist 2 (by decide)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y ≤ edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by simp only [edist_comm]; ac_rfl
    _ ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = edist x' y' + 2 * edist (x, y) (x', y') := by rw [← mul_two, mul_comm]

@[continuity, fun_prop]
theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prodMk hg :)

theorem Filter.Tendsto.edist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `NNReal`s, then the original sequence is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_of_summable {f : ℕ → α} (d : ℕ → ℝ≥0)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : Summable d) : CauchySeq f := by
  refine EMetric.cauchySeq_iff_NNReal.2 fun ε εpos ↦ ?_
  -- Actually we need partial sums of `d` to be a Cauchy sequence.
  replace hd : CauchySeq fun n : ℕ ↦ ∑ x ∈ Finset.range n, d x :=
    let ⟨_, H⟩ := hd
    H.tendsto_sum_nat.cauchySeq
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence.
  refine (Metric.cauchySeq_iff'.1 hd ε (NNReal.coe_pos.2 εpos)).imp fun N hN n hn ↦ ?_
  specialize hN n hn
  -- We simplify the known inequality.
  rw [dist_nndist, NNReal.nndist_eq, ← Finset.sum_range_add_sum_Ico _ hn, add_tsub_cancel_left,
    NNReal.coe_lt_coe, max_lt_iff] at hN
  rw [edist_comm]
  -- Then use `hf` to simplify the goal to the same form.
  refine lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn fun _ _ ↦ hf _) ?_
  exact mod_cast hN.1

theorem cauchySeq_of_edist_le_of_tsum_ne_top {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : tsum d ≠ ∞) : CauchySeq f := by
  lift d to ℕ → NNReal using fun i => ENNReal.ne_top_of_tsum_ne_top hd i
  rw [ENNReal.tsum_coe_ne_top_iff_summable] at hd
  exact cauchySeq_of_edist_le_of_summable d hf hd

theorem EMetric.isClosed_closedBall {a : α} {r : ℝ≥0∞} : IsClosed (closedBall a r) :=
  isClosed_le (continuous_id.edist continuous_const) continuous_const

@[simp]
theorem EMetric.diam_closure (s : Set α) : diam (closure s) = diam s := by
  refine le_antisymm (diam_le fun x hx y hy => ?_) (diam_mono subset_closure)
  have : edist x y ∈ closure (Iic (diam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_diam_of_mem hx hy
  rwa [closure_Iic] at this

@[simp]
theorem Metric.diam_closure {α : Type*} [PseudoMetricSpace α] (s : Set α) :
    Metric.diam (closure s) = diam s := by simp only [Metric.diam, EMetric.diam_closure]

theorem isClosed_setOf_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0)
    (s : Set α) : IsClosed { f : α → β | LipschitzOnWith K f s } := by
  simp only [LipschitzOnWith, setOf_forall]
  refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
  exacts [.edist (continuous_apply x) (continuous_apply y), continuous_const]

theorem isClosed_setOf_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) :
    IsClosed { f : α → β | LipschitzWith K f } := by
  simp only [← lipschitzOnWith_univ, isClosed_setOf_lipschitzOnWith]

namespace Real

/-- For a bounded set `s : Set ℝ`, its `EMetric.diam` is equal to `sSup s - sInf s` reinterpreted as
`ℝ≥0∞`. -/
theorem ediam_eq {s : Set ℝ} (h : Bornology.IsBounded s) :
    EMetric.diam s = ENNReal.ofReal (sSup s - sInf s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  refine le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) ?_
  · exact Real.dist_le_of_mem_Icc (h.subset_Icc_sInf_sSup hx) (h.subset_Icc_sInf_sSup hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam, ← Metric.diam_closure]
    calc sSup s - sInf s ≤ dist (sSup s) (sInf s) := le_abs_self _
    _ ≤ Metric.diam (closure s) := dist_le_diam_of_mem h.closure (csSup_mem_closure hne h.bddAbove)
        (csInf_mem_closure hne h.bddBelow)

/-- For a bounded set `s : Set ℝ`, its `Metric.diam` is equal to `sSup s - sInf s`. -/
theorem diam_eq {s : Set ℝ} (h : Bornology.IsBounded s) : Metric.diam s = sSup s - sInf s := by
  rw [Metric.diam, Real.ediam_eq h, ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.bddBelow h.bddAbove)

@[simp]
theorem ediam_Ioo (a b : ℝ) : EMetric.diam (Ioo a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (isBounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]

@[simp]
theorem ediam_Icc (a b : ℝ) : EMetric.diam (Icc a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt a b with (h | h)
  · rw [Real.ediam_eq (isBounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]

@[simp]
theorem ediam_Ico (a b : ℝ) : EMetric.diam (Ico a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ diam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ico_self)

@[simp]
theorem ediam_Ioc (a b : ℝ) : EMetric.diam (Ioc a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ diam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ diam_mono Ioo_subset_Ioc_self)

theorem diam_Icc {a b : ℝ} (h : a ≤ b) : Metric.diam (Icc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem diam_Ico {a b : ℝ} (h : a ≤ b) : Metric.diam (Ico a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem diam_Ioc {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem diam_Ioo {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioo a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

end Real

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f n` to the limit is bounded by `∑'_{k=n}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ ∑' m, d (n + m) := by
  refine le_of_tendsto (tendsto_const_nhds.edist ha) (mem_atTop_sets.2 ⟨n, fun m hnm => ?_⟩)
  change edist _ _ ≤ _
  refine le_trans (edist_le_Ico_sum_of_edist_le hnm fun _ _ => hf _) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  exact ENNReal.summable.sum_le_tsum _ (fun _ _ => zero_le _)

/-- If `edist (f n) (f (n+1))` is bounded above by a function `d : ℕ → ℝ≥0∞`,
then the distance from `f 0` to the limit is bounded by `∑'_{k=0}^∞ d k`. -/
theorem edist_le_tsum_of_edist_le_of_tendsto₀ {f : ℕ → α} (d : ℕ → ℝ≥0∞)
    (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ ∑' m, d m := by simpa using edist_le_tsum_of_edist_le_of_tendsto d hf ha 0

end

namespace ENNReal

section truncateToReal

/-- With truncation level `t`, the truncated cast `ℝ≥0∞ → ℝ` is given by `x ↦ (min t x).toReal`.
Unlike `ENNReal.toReal`, this cast is continuous and monotone when `t ≠ ∞`. -/
noncomputable def truncateToReal (t x : ℝ≥0∞) : ℝ := (min t x).toReal

lemma truncateToReal_eq_toReal {t x : ℝ≥0∞} (t_ne_top : t ≠ ∞) (x_le : x ≤ t) :
    truncateToReal t x = x.toReal := by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x ≠ ∞ := by
    simp_all only [ne_eq, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal obs x_lt_top.ne).mpr (min_eq_right x_le)

lemma truncateToReal_le {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) {x : ℝ≥0∞} :
    truncateToReal t x ≤ t.toReal := by
  rw [truncateToReal]
  gcongr
  exacts [t_ne_top, min_le_left t x]

lemma truncateToReal_nonneg {t x : ℝ≥0∞} : 0 ≤ truncateToReal t x := toReal_nonneg

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is monotone when `t ≠ ∞`. -/
lemma monotone_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) : Monotone (truncateToReal t) := by
  intro x y x_le_y
  simp only [truncateToReal]
  gcongr
  exact ne_top_of_le_ne_top t_ne_top (min_le_left _ _)

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is continuous when `t ≠ ∞`. -/
@[fun_prop]
lemma continuous_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) : Continuous (truncateToReal t) := by
  apply continuousOn_toReal.comp_continuous (by fun_prop)
  simp [t_ne_top]

end truncateToReal

section LimsupLiminf

variable {ι : Type*} {f : Filter ι} {u v : ι → ℝ≥0∞}

lemma limsup_sub_const (F : Filter ι) (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    Filter.limsup (fun i ↦ f i - c) F = Filter.limsup f F - c := by
  rcases F.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', zero_le, tsub_eq_zero_of_le]
  · exact (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

lemma liminf_sub_const (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    Filter.liminf (fun i ↦ f i - c) F = Filter.liminf f F - c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt).symm

lemma limsup_const_sub (F : Filter ι) (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    Filter.limsup (fun i ↦ c - f i) F = c - Filter.liminf f F := by
  rcases F.eq_or_neBot with rfl | _
  · simp only [limsup_bot, bot_eq_zero', liminf_bot, le_top, tsub_eq_zero_of_le]
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

lemma liminf_const_sub (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    Filter.liminf (fun i ↦ c - f i) F = c - Filter.limsup f F :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c_ne_top).continuousAt).symm

lemma le_limsup_mul : limsup u f * liminf v f ≤ limsup (u * v) f :=
  mul_le_of_forall_lt fun a a_u b b_v ↦ (le_limsup_iff).2 fun c c_ab ↦
    Frequently.mono (Frequently.and_eventually ((frequently_lt_of_lt_limsup) a_u)
    ((eventually_lt_of_lt_liminf) b_v)) fun _ ab_x ↦ c_ab.trans (mul_lt_mul ab_x.1 ab_x.2)

/-- See also `ENNReal.limsup_mul_le`. -/
lemma limsup_mul_le' (h : limsup u f ≠ 0 ∨ limsup v f ≠ ∞) (h' : limsup u f ≠ ∞ ∨ limsup v f ≠ 0) :
    limsup (u * v) f ≤ limsup u f * limsup v f := by
  refine le_mul_of_forall_lt h h' fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (mul_lt_mul a_x b_x).trans c_ab

lemma le_liminf_mul : liminf u f * liminf v f ≤ liminf (u * v) f := by
  refine mul_le_of_forall_lt fun a a_u b b_v ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (mul_lt_mul a_x b_x)

lemma liminf_mul_le (h : limsup u f ≠ 0 ∨ liminf v f ≠ ∞) (h' : limsup u f ≠ ∞ ∨ liminf v f ≠ 0) :
    liminf (u * v) f ≤ limsup u f * liminf v f :=
  le_mul_of_forall_lt h h' fun a a_u b b_v ↦ (liminf_le_iff).2 fun c c_ab ↦
    Frequently.mono (((frequently_lt_of_liminf_lt) b_v).and_eventually
    ((eventually_lt_of_limsup_lt) a_u)) fun _ ab_x ↦ (mul_lt_mul ab_x.2 ab_x.1).trans c_ab

/-- If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf u)`. -/
lemma liminf_toReal_eq [NeBot f] {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) (le_b : ∀ᶠ i in f, u i ≤ b) :
    f.liminf (fun i ↦ (u i).toReal) = (f.liminf u).toReal := by
  have liminf_le : f.liminf u ≤ b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y h
    obtain ⟨i, hi⟩ := (Eventually.and h le_b).exists
    exact hi.1.trans hi.2
  have aux : ∀ᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.liminf u).toReal = ENNReal.truncateToReal b (f.liminf u) := by
    rw [truncateToReal_eq_toReal b_ne_top liminf_le]
  simp_rw [liminf_congr aux, aux']
  have key := Monotone.map_liminf_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          (IsBoundedUnder.isCoboundedUnder_ge ⟨b, by simpa only [eventually_map] using le_b⟩)
          ⟨0, Eventually.of_forall (by simp)⟩
  rw [key]
  rfl

/-- If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf u)`. -/
lemma limsup_toReal_eq [NeBot f] {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) (le_b : ∀ᶠ i in f, u i ≤ b) :
    f.limsup (fun i ↦ (u i).toReal) = (f.limsup u).toReal := by
  have aux : ∀ᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.limsup u).toReal = ENNReal.truncateToReal b (f.limsup u) := by
    rw [truncateToReal_eq_toReal b_ne_top (limsup_le_of_le ⟨0, by simp⟩ le_b)]
  simp_rw [limsup_congr aux, aux']
  have key := Monotone.map_limsup_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          ⟨b, by simpa only [eventually_map] using le_b⟩
          (IsBoundedUnder.isCoboundedUnder_le ⟨0, Eventually.of_forall (by simp)⟩)
  rw [key]
  rfl

@[simp, norm_cast]
lemma ofNNReal_limsup {u : ι → ℝ≥0} (hf : f.IsBoundedUnder (· ≤ ·) u) :
    limsup u f = limsup (fun i ↦ (u i : ℝ≥0∞)) f := by
  refine eq_of_forall_nnreal_iff fun r ↦ ?_
  rw [coe_le_coe, le_limsup_iff, le_limsup_iff]
  simp [forall_ennreal]

@[simp, norm_cast]
lemma ofNNReal_liminf {u : ι → ℝ≥0} (hf : f.IsCoboundedUnder (· ≥ ·) u) :
    liminf u f = liminf (fun i ↦ (u i : ℝ≥0∞)) f := by
  refine eq_of_forall_nnreal_iff fun r ↦ ?_
  rw [coe_le_coe, le_liminf_iff, le_liminf_iff]
  simp [forall_ennreal]

theorem liminf_add_of_right_tendsto_zero {u : Filter ι} {g : ι → ℝ≥0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι → ℝ≥0∞) : u.liminf (f + g) = u.liminf f := by
  refine le_antisymm ?_ <| liminf_le_liminf <| .of_forall <| by simp
  refine liminf_le_of_le (by isBoundedDefault) fun b hb ↦ ?_
  rw [Filter.le_liminf_iff']
  rintro a hab
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| lt_min (tsub_pos_of_lt hab) one_pos]
    with i hfg hg
  exact ENNReal.le_of_add_le_add_right (hg.trans_lt <| by simp).ne <|
    (add_le_of_le_tsub_left_of_le hab.le <| hg.trans <| min_le_left ..).trans hfg

theorem liminf_add_of_left_tendsto_zero {u : Filter ι} {f : ι → ℝ≥0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι → ℝ≥0∞) : u.liminf (f + g) = u.liminf g := by
  rw [add_comm, liminf_add_of_right_tendsto_zero hf]

theorem limsup_add_of_right_tendsto_zero {u : Filter ι} {g : ι → ℝ≥0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι → ℝ≥0∞) : u.limsup (f + g) = u.limsup f := by
  refine le_antisymm ?_ <| limsup_le_limsup <| .of_forall <| by simp
  refine le_limsup_of_le (by isBoundedDefault) fun b hb ↦ ?_
  rw [Filter.limsup_le_iff']
  rintro a hba
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| tsub_pos_of_lt hba] with i hf hg
  calc  f i + g i
    _ ≤ b + g i := by gcongr
    _ ≤ a := add_le_of_le_tsub_left_of_le hba.le hg

theorem limsup_add_of_left_tendsto_zero {u : Filter ι} {f : ι → ℝ≥0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι → ℝ≥0∞) : u.limsup (f + g) = u.limsup g := by
  rw [add_comm, limsup_add_of_right_tendsto_zero hf]

end LimsupLiminf

end ENNReal -- namespace
