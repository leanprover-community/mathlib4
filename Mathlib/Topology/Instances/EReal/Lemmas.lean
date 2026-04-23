/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.IsBounded
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Topological structure on `EReal`

We prove basic properties of the topology on `EReal`.

## Main results

* `Real.toEReal : ℝ → EReal` is an open embedding
* `ENNReal.toEReal : ℝ≥0∞ → EReal` is a closed embedding
* The addition on `EReal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `EReal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric TopologicalSpace Topology
open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal

/-! ### Real coercion -/

theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ → EReal) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ → EReal) :=
  ⟨isEmbedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩

@[norm_cast]
theorem tendsto_coe {α : Type*} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm

theorem _root_.continuous_coe_real_ereal : Continuous ((↑) : ℝ → EReal) :=
  isEmbedding_coe.continuous

theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm

theorem nhds_coe {r : ℝ} : 𝓝 (r : EReal) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

theorem nhds_coe_coe {r p : ℝ} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) := by
  lift a to ℝ using ⟨ha, h'a⟩
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))

/-- The set of finite `EReal` numbers is homeomorphic to `ℝ`. -/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ where
  toEquiv := neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _

/-! ### ENNReal coercion -/

theorem isEmbedding_coe_ennreal : IsEmbedding ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.isEmbedding_of_ordConnected <| by
    rw [range_coe_ennreal]; exact ordConnected_Ici

theorem isClosedEmbedding_coe_ennreal : IsClosedEmbedding ((↑) : ℝ≥0∞ → EReal) :=
  ⟨isEmbedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]
theorem tendsto_coe_ennreal {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe_ennreal.tendsto_nhds_iff.symm

theorem _root_.continuous_coe_ennreal_ereal : Continuous ((↑) : ℝ≥0∞ → EReal) :=
  isEmbedding_coe_ennreal.continuous

theorem continuous_coe_ennreal_iff {f : α → ℝ≥0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  isEmbedding_coe_ennreal.continuous_iff.symm

/-! ### Neighborhoods of infinity -/

theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp only [lt_top_iff_ne_top]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Ioi ·) := by
  refine (nhds_top_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ ↦ ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, hxy, -⟩
  exact ⟨_, trivial, Ioi_subset_Ioi hxy.le⟩

theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi ↑a) := nhds_top_basis.eq_iInf

theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s :=
  nhds_top_basis.mem_iff.trans <| by simp only [true_and]

theorem tendsto_nhds_top_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
  nhds_top_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Ioi]

theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]

theorem nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Iio ·) := by
  refine (_root_.nhds_bot_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ ↦ ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩

theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : ℝ, 𝓟 (Iio ↑a) :=
  nhds_bot_basis.eq_iInf

theorem mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 (⊥ : EReal) ↔ ∃ y : ℝ, Iio (y : EReal) ⊆ s :=
  nhds_bot_basis.mem_iff.trans <| by simp only [true_and]

theorem tendsto_nhds_bot_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x :=
  nhds_bot_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Iio]

lemma nhdsWithin_top : 𝓝[≠] (⊤ : EReal) = (atTop).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to ℝ using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h1, h2.ne_top]
  · simp only [EReal.image_coe_Ici, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.coe_lt_top x, fun x ⟨(h1 : _ ≤ x), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.lt_top' fun a ↦ h2 a.symm]

lemma nhdsWithin_bot : 𝓝[≠] (⊥ : EReal) = (atBot).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic,
      true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to ℝ using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h2, h1.ne_bot]
  · simp only [EReal.image_coe_Iic, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.bot_lt_coe x, fun x ⟨(h1 : x ≤ _), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.bot_lt' fun a ↦ h2 a.symm]

omit [TopologicalSpace α] in
@[simp]
lemma tendsto_coe_nhds_top_iff {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_real, atTop_basis_Ioi.tendsto_right_iff]; simp

lemma tendsto_coe_atTop : Tendsto Real.toEReal atTop (𝓝 ⊤) :=
  tendsto_coe_nhds_top_iff.2 tendsto_id

omit [TopologicalSpace α] in
@[simp]
lemma tendsto_coe_nhds_bot_iff {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l atBot := by
  rw [tendsto_nhds_bot_iff_real, atBot_basis_Iio.tendsto_right_iff]; simp

lemma tendsto_coe_atBot : Tendsto Real.toEReal atBot (𝓝 ⊥) :=
  tendsto_coe_nhds_bot_iff.2 tendsto_id


lemma tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[≠] ⊤) atTop := by
  rw [nhdsWithin_top, tendsto_map'_iff]
  exact tendsto_id

lemma tendsto_toReal_atBot : Tendsto EReal.toReal (𝓝[≠] ⊥) atBot := by
  rw [nhdsWithin_bot, tendsto_map'_iff]
  exact tendsto_id

/-! ### toENNReal -/

lemma continuous_toENNReal : Continuous EReal.toENNReal := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases h_top : x = ⊤
  · simp only [ContinuousAt, h_top, toENNReal_top]
    refine ENNReal.tendsto_nhds_top fun n ↦ ?_
    filter_upwards [eventually_gt_nhds (coe_lt_top n)] with y hy
    exact toENNReal_coe (x := n) ▸ toENNReal_lt_toENNReal (coe_ennreal_nonneg _) hy
  refine ContinuousOn.continuousAt ?_ (compl_singleton_mem_nhds_iff.mpr h_top)
  refine (continuousOn_of_forall_continuousAt fun x hx ↦ ?_).congr (fun _ h ↦ toENNReal_of_ne_top h)
  by_cases h_bot : x = ⊥
  · refine tendsto_nhds_of_eventually_eq ?_
    rw [h_bot, nhds_bot_basis.eventually_iff]
    simpa [toReal_bot, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero, true_and] using
      ⟨0, fun _ hx ↦ toReal_nonpos hx.le⟩
  refine ENNReal.continuous_ofReal.continuousAt.comp' <| continuousOn_toReal.continuousAt
    <| (toFinite _).isClosed.compl_mem_nhds ?_
  simp_all only [mem_compl_iff, mem_singleton_iff, mem_insert_iff, or_self, not_false_eq_true]

@[fun_prop]
lemma _root_.Continuous.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    (hf : Continuous f) :
    Continuous fun x => (f x).toENNReal :=
  continuous_toENNReal.comp hf

@[fun_prop]
lemma _root_.ContinuousOn.ereal_toENNReal {α : Type*} [TopologicalSpace α] {s : Set α}
    {f : α → EReal} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).toENNReal) s :=
  continuous_toENNReal.comp_continuousOn hf

@[fun_prop]
lemma _root_.ContinuousWithinAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x).toENNReal) s x :=
  continuous_toENNReal.continuousAt.comp_continuousWithinAt hf

@[fun_prop]
lemma _root_.ContinuousAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (f x).toENNReal) x :=
  continuous_toENNReal.continuousAt.comp hf

/-! ### Infs and Sups -/

variable {α : Type*} {u v : α → EReal}

lemma add_iInf_le_iInf_add : (⨅ x, u x) + ⨅ x, v x ≤ ⨅ x, (u + v) x :=
  le_iInf fun i ↦ add_le_add (iInf_le u i) (iInf_le v i)

lemma iSup_add_le_add_iSup : ⨆ x, (u + v) x ≤ (⨆ x, u x) + ⨆ x, v x :=
  iSup_le fun i ↦ add_le_add (le_iSup u i) (le_iSup v i)

/-! ### Liminfs and Limsups -/

section LimInfSup

variable {α : Type*} {f : Filter α} {u v : α → EReal}

lemma liminf_neg : liminf (-v) f = -limsup v f :=
  EReal.negOrderIso.limsup_apply.symm

lemma limsup_neg : limsup (-v) f = -liminf v f :=
  EReal.negOrderIso.liminf_apply.symm

lemma le_liminf_add : (liminf u f) + (liminf v f) ≤ liminf (u + v) f := by
  refine add_le_of_forall_lt fun a a_u b b_v ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)

lemma limsup_add_le (h : limsup u f ≠ ⊥ ∨ limsup v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ limsup v f ≠ ⊥) :
    limsup (u + v) f ≤ (limsup u f) + (limsup v f) := by
  refine le_add_of_forall_gt h h' fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab

lemma le_limsup_add : (limsup u f) + (liminf v f) ≤ limsup (u + v) f :=
  add_le_of_forall_lt fun _ a_u _ b_v ↦ (le_limsup_iff).2 fun _ c_ab ↦
    (((frequently_lt_of_lt_limsup) a_u).and_eventually ((eventually_lt_of_lt_liminf) b_v)).mono
    fun _ ab_x ↦ c_ab.trans (add_lt_add ab_x.1 ab_x.2)

lemma liminf_add_le (h : limsup u f ≠ ⊥ ∨ liminf v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ liminf v f ≠ ⊥) :
    liminf (u + v) f ≤ (limsup u f) + (liminf v f) :=
  le_add_of_forall_gt h h' fun _ a_u _ b_v ↦ (liminf_le_iff).2 fun _ c_ab ↦
    (((frequently_lt_of_liminf_lt) b_v).and_eventually ((eventually_lt_of_limsup_lt) a_u)).mono
    fun _ ab_x ↦ (add_lt_add ab_x.2 ab_x.1).trans c_ab

lemma limsup_add_bot_of_ne_top (h : limsup u f = ⊥) (h' : limsup v f ≠ ⊤) :
    limsup (u + v) f = ⊥ := by
  apply le_bot_iff.1 ((limsup_add_le (.inr h') _).trans _)
  · rw [h]; exact .inl bot_ne_top
  · rw [h, bot_add]

lemma limsup_add_le_of_le {a b : EReal} (ha : limsup u f < a) (hb : limsup v f ≤ b) :
    limsup (u + v) f ≤ a + b := by
  rcases eq_top_or_lt_top b with rfl | h
  · rw [add_top_of_ne_bot ha.ne_bot]; exact le_top
  · exact (limsup_add_le (.inr (hb.trans_lt h).ne) (.inl ha.ne_top)).trans (add_le_add ha.le hb)

lemma liminf_add_gt_of_gt {a b : EReal} (ha : a < liminf u f) (hb : b < liminf v f) :
    a + b < liminf (u + v) f :=
  (add_lt_add ha hb).trans_le le_liminf_add

lemma liminf_add_top_of_ne_bot (h : liminf u f = ⊤) (h' : liminf v f ≠ ⊥) :
    liminf (u + v) f = ⊤ := by
  apply top_le_iff.1 (le_trans _ le_liminf_add)
  rw [h, top_add_of_ne_bot h']

theorem limsup_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 ≤ c) (h₂ : c ≠ ⊤) :
    limsup (fun x => c * u x) f = c * limsup u f := by
  obtain rfl | h₃ := h₁.eq_or_lt
  · simp
  simp_rw [EReal.mul_comm (x := c)]
  apply eq_of_le_of_ge
  · rw [limsup_le_iff]
    simpa [← EReal.lt_div_iff (by aesop) (by aesop)]
      using fun _ ↦ eventually_lt_of_limsup_lt
  · rw [le_limsup_iff]
    simpa [← EReal.div_lt_iff (by aesop) (by aesop)]
      using fun _ ↦ frequently_lt_of_lt_limsup

theorem limsup_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c ≤ 0) (h₂ : c ≠ ⊥) :
    limsup (fun x => c * u x) f = c * liminf u f := by
  simpa [limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (c := -c) (by aesop) (by aesop)

theorem liminf_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 ≤ c) (h₂ : c ≠ ⊤) :
    liminf (fun x => c * u x) f = c * liminf u f := by
  simpa [mul_neg, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (by aesop) (by aesop)

theorem liminf_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c ≤ 0) (h₂ : c ≠ ⊥) :
    liminf (fun x => c * u x) f = c * limsup u f := by
  simpa [neg_mul, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (c := -c) (by aesop) (by aesop)

lemma le_limsup_mul (hu : ∃ᶠ x in f, 0 ≤ u x) (hv : 0 ≤ᶠ[f] v) :
    limsup u f * liminf v f ≤ limsup (u * v) f := by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot, limsup_bot, liminf_bot, bot_mul_top]
  have u0 : 0 ≤ limsup u f := le_limsup_of_frequently_le hu
  have uv0 : 0 ≤ limsup (u * v) f :=
    le_limsup_of_frequently_le <| (hu.and_eventually hv).mono fun _ ⟨hu, hv⟩ ↦ mul_nonneg hu hv
  refine mul_le_of_forall_lt_of_nonneg u0 uv0 fun a ha b hb ↦ (le_limsup_iff).2 fun c c_ab ↦ ?_
  refine (((frequently_lt_of_lt_limsup) (mem_Ioo.1 ha).2).and_eventually
    <| (eventually_lt_of_lt_liminf (mem_Ioo.1 hb).2).and
    <| hv).mono fun x ⟨xa, ⟨xb, vx⟩⟩ ↦ ?_
  exact c_ab.trans_le (mul_le_mul xa.le xb.le (mem_Ioo.1 hb).1.le ((mem_Ioo.1 ha).1.le.trans xa.le))

lemma limsup_mul_le (hu : ∃ᶠ x in f, 0 ≤ u x) (hv : 0 ≤ᶠ[f] v)
    (h₁ : limsup u f ≠ 0 ∨ limsup v f ≠ ⊤) (h₂ : limsup u f ≠ ⊤ ∨ limsup v f ≠ 0) :
    limsup (u * v) f ≤ limsup u f * limsup v f := by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot]; exact bot_le
  have u_0 : 0 ≤ limsup u f := le_limsup_of_frequently_le hu
  replace h₁ : 0 < limsup u f ∨ limsup v f ≠ ⊤ := h₁.imp_left fun h ↦ lt_of_le_of_ne u_0 h.symm
  replace h₂ : limsup u f ≠ ⊤ ∨ 0 < limsup v f :=
    h₂.imp_right fun h ↦ lt_of_le_of_ne (le_limsup_of_frequently_le hv.frequently) h.symm
  refine le_mul_of_forall_lt h₁ h₂ fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v, hv]
    with x x_a x_b v_0
  apply lt_of_le_of_lt _ c_ab
  rcases lt_or_ge (u x) 0 with hux | hux
  · apply (mul_nonpos_iff.2 (.inr ⟨hux.le, v_0⟩)).trans
    exact mul_nonneg (u_0.trans a_u.le) (v_0.trans x_b.le)
  · exact mul_le_mul x_a.le x_b.le v_0 (hux.trans x_a.le)

lemma le_liminf_mul (hu : 0 ≤ᶠ[f] u) (hv : 0 ≤ᶠ[f] v) :
    liminf u f * liminf v f ≤ liminf (u * v) f := by
  apply mul_le_of_forall_lt_of_nonneg ((le_liminf_of_le) hu)
    <| (le_liminf_of_le) ((hu.and hv).mono fun x ⟨u0, v0⟩ ↦ mul_nonneg u0 v0)
  refine fun a ha b hb ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf (mem_Ioo.1 ha).2,
    eventually_lt_of_lt_liminf (mem_Ioo.1 hb).2] with x xa xb
  exact c_ab.trans_le (mul_le_mul xa.le xb.le (mem_Ioo.1 hb).1.le ((mem_Ioo.1 ha).1.le.trans xa.le))

lemma liminf_mul_le [NeBot f] (hu : 0 ≤ᶠ[f] u) (hv : 0 ≤ᶠ[f] v)
    (h₁ : limsup u f ≠ 0 ∨ liminf v f ≠ ⊤) (h₂ : limsup u f ≠ ⊤ ∨ liminf v f ≠ 0) :
    liminf (u * v) f ≤ limsup u f * liminf v f := by
  replace h₁ : 0 < limsup u f ∨ liminf v f ≠ ⊤ := by
    refine h₁.imp_left fun h ↦ lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (limsup_const 0).symm (limsup_le_limsup hu)
  replace h₂ : limsup u f ≠ ⊤ ∨ 0 < liminf v f := by
    refine h₂.imp_right fun h ↦ lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (liminf_const 0).symm (liminf_le_liminf hv)
  refine le_mul_of_forall_lt h₁ h₂ fun a a_u b b_v ↦ (liminf_le_iff).2 fun c c_ab ↦ ?_
  refine (((frequently_lt_of_liminf_lt) b_v).and_eventually <| (eventually_lt_of_limsup_lt a_u).and
    <| hu.and hv).mono fun x ⟨x_v, x_u, u_0, v_0⟩ ↦ ?_
  exact (mul_le_mul x_u.le x_v.le v_0 (u_0.trans x_u.le)).trans_lt c_ab

end LimInfSup

/-! ### Continuity of addition -/

theorem continuousAt_add_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, Function.comp_def,
    tendsto_coe, tendsto_add]

theorem continuousAt_add_top_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

theorem continuousAt_add_coe_top (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) := by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))

theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

theorem continuousAt_add_bot_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

theorem continuousAt_add_coe_bot (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) := by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))

theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

/-- The addition on `EReal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
theorem continuousAt_add {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_add_bot_bot
  · exact continuousAt_add_bot_coe _
  · simp at h'
  · exact continuousAt_add_coe_bot _
  · exact continuousAt_add_coe_coe _ _
  · exact continuousAt_add_coe_top _
  · simp at h
  · exact continuousAt_add_top_coe _
  · exact continuousAt_add_top_top

lemma lowerSemicontinuous_add : LowerSemicontinuous fun p : EReal × EReal ↦ p.1 + p.2 := by
  intro x y
  by_cases hx₁ : x.1 = ⊥
  · simp [hx₁]
  by_cases hx₂ : x.2 = ⊥
  · simp [hx₂]
  · exact continuousAt_add (.inr hx₂) (.inl hx₁) |>.lowerSemicontinuousAt _

/-! ### Continuity of multiplication -/

/- Outside of indeterminacies `(0, ±∞)` and `(±∞, 0)`, the multiplication on `EReal` is continuous.
There are many different cases to consider, so we first prove some special cases and leverage as
much as possible the symmetries of the multiplication. -/

private lemma continuousAt_mul_swap {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (b, a) := by
  convert h.comp continuous_swap.continuousAt (x := (b, a))
  simp [mul_comm]

private lemma continuousAt_mul_symm1 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, b) := by
  have : (fun p : EReal × EReal ↦ p.1 * p.2) = (fun x : EReal ↦ -x)
      ∘ (fun p : EReal × EReal ↦ p.1 * p.2) ∘ (fun p : EReal × EReal ↦ (-p.1, p.2)) := by
    ext p
    simp
  rw [this]
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
    <| ContinuousAt.comp _ (ContinuousAt.prodMap (Continuous.continuousAt continuous_neg)
      (Continuous.continuousAt continuous_id))
  simp [h]

private lemma continuousAt_mul_symm2 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, -b) :=
  continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))

private lemma continuousAt_mul_symm3 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, -b) :=
  continuousAt_mul_symm1 (continuousAt_mul_symm2 h)

private lemma continuousAt_mul_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b) := by
  simp [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    Function.comp_def, EReal.tendsto_coe, tendsto_mul]

private lemma continuousAt_mul_top_top :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
    rcases p_in_prod with ⟨⟨p1_gt_x, p1_pos⟩, p2_gt_1⟩
    have := mul_le_mul_of_nonneg_left (le_of_lt p2_gt_1) (le_of_lt p1_pos)
    rw [mul_one p.1] at this
    exact lt_of_lt_of_le p1_gt_x this
  · exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  · simp
  · rw [Set.mem_Ioi, ← EReal.coe_one]; exact EReal.coe_lt_top 1

private lemma continuousAt_mul_top_pos {a : ℝ} (h : 0 < a) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((2 * (max (x + 1) 0) / a : ℝ) : EReal)) ×ˢ (Set.Ioi ((a / 2 : ℝ) : EReal))
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi] at p_in_prod
    rcases p_in_prod with ⟨p1_gt, p2_gt⟩
    have p1_pos : 0 < p.1 := by
      apply lt_of_le_of_lt _ p1_gt
      rw [EReal.coe_nonneg]
      apply mul_nonneg _ (le_of_lt (inv_pos_of_pos h))
      simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, le_max_iff, le_refl, or_true]
    have a2_pos : 0 < ((a / 2 : ℝ) : EReal) := by rw [EReal.coe_pos]; linarith
    have lock := mul_le_mul_of_nonneg_right (le_of_lt p1_gt) (le_of_lt a2_pos)
    have key := mul_le_mul_of_nonneg_left (le_of_lt p2_gt) (le_of_lt p1_pos)
    replace lock := le_trans lock key
    apply lt_of_lt_of_le _ lock
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, _root_.div_mul_div_comm, mul_comm,
      ← _root_.div_mul_div_comm, mul_div_right_comm]
    simp only [ne_eq, Ne.symm (ne_of_lt h), not_false_eq_true, _root_.div_self, OfNat.ofNat_ne_zero,
      one_mul, lt_max_iff, lt_add_iff_pos_right, zero_lt_one, true_or]
  · exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  · simp
  · simp [h]

private lemma continuousAt_mul_top_ne_zero {a : ℝ} (h : a ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  rcases lt_or_gt_of_ne h with a_neg | a_pos
  · exact neg_neg a ▸ continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  · exact continuousAt_mul_top_pos a_pos

/-- The multiplication on `EReal` is continuous except at indeterminacies
(i.e. whenever one value is zero and the other infinite). -/
theorem continuousAt_mul {p : EReal × EReal} (h₁ : p.1 ≠ 0 ∨ p.2 ≠ ⊥)
    (h₂ : p.1 ≠ 0 ∨ p.2 ≠ ⊤) (h₃ : p.1 ≠ ⊥ ∨ p.2 ≠ 0) (h₄ : p.1 ≠ ⊤ ∨ p.2 ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_mul_symm3 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃
    exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  · exact EReal.neg_top ▸ continuousAt_mul_symm1 continuousAt_mul_top_top
  · simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₁
    exact continuousAt_mul_symm2 (continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₁))
  · exact continuousAt_mul_coe_coe _ _
  · simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₂
    exact continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₂)
  · exact continuousAt_mul_symm2 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₄
    exact continuousAt_mul_top_ne_zero h₄
  · exact continuousAt_mul_top_top

variable {a b : EReal}

protected theorem tendsto_mul (h₁ : a ≠ 0 ∨ b ≠ ⊥) (h₂ : a ≠ 0 ∨ b ≠ ⊤) (h₃ : a ≠ ⊥ ∨ b ≠ 0)
    (h₄ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun p : EReal × EReal ↦ p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
  (continuousAt_mul h₁ h₂ h₃ h₄).tendsto

protected theorem Tendsto.mul {f : Filter α} {ma : α → EReal} {mb : α → EReal} {a b : EReal}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h₁ : a ≠ 0 ∨ b ≠ ⊥)
    (h₂ : a ≠ 0 ∨ b ≠ ⊤) (h₃ : a ≠ ⊥ ∨ b ≠ 0) (h₄ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun x ↦ ma x * mb x) f (𝓝 (a * b)) :=
  (EReal.tendsto_mul h₁ h₂ h₃ h₄).comp (hma.prodMk_nhds hmb)

protected theorem Tendsto.const_mul {f : Filter α} {m : α → EReal} {a b : EReal}
    (hm : Tendsto m f (𝓝 b)) (h₁ : a ≠ ⊥ ∨ b ≠ 0) (h₂ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun b ↦ a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds])
    fun ha : a ≠ 0 => EReal.Tendsto.mul tendsto_const_nhds hm (Or.inl ha) (Or.inl ha) h₁ h₂

protected theorem Tendsto.mul_const {f : Filter α} {m : α → EReal} {a b : EReal}
    (hm : Tendsto m f (𝓝 a)) (h₁ : a ≠ 0 ∨ b ≠ ⊥) (h₂ : a ≠ 0 ∨ b ≠ ⊤) :
    Tendsto (fun x ↦ m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using EReal.Tendsto.const_mul hm h₁.symm h₂.symm

end EReal
