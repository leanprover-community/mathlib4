/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.EReal
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Order.MonotoneContinuity

#align_import topology.instances.ereal from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Topological structure on `EReal`

We endow `EReal` with the order topology, and prove basic properties of this topology.

## Main results

* `Real.toEReal : ℝ → EReal` is an open embedding
* `ENNReal.toEReal : ℝ≥0∞ → EReal` is a closed embedding
* The addition on `EReal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `EReal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

noncomputable section

open scoped Classical
open Set Filter Metric TopologicalSpace Topology
open scoped ENNReal NNReal Filter

variable {α : Type*} [TopologicalSpace α]

namespace EReal

instance : TopologicalSpace EReal := Preorder.topology EReal
instance : OrderTopology EReal := ⟨rfl⟩
instance : T5Space EReal := inferInstance
instance : T2Space EReal := inferInstance

lemma denseRange_ratCast : DenseRange (fun r : ℚ ↦ ((r : ℝ) : EReal)) :=
  dense_of_exists_between fun _ _ h => exists_range_iff.2 <| exists_rat_btwn_of_lt h

instance : SecondCountableTopology EReal :=
  have : SeparableSpace EReal := ⟨⟨_, countable_range _, denseRange_ratCast⟩⟩
  .of_separableSpace_orderTopology _

/-! ### Real coercion -/

theorem embedding_coe : Embedding ((↑) : ℝ → EReal) :=
  coe_strictMono.embedding_of_ordConnected <| by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo
#align ereal.embedding_coe EReal.embedding_coe

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℝ → EReal) :=
  ⟨embedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩
#align ereal.open_embedding_coe EReal.openEmbedding_coe

@[norm_cast]
theorem tendsto_coe {α : Type*} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm
#align ereal.tendsto_coe EReal.tendsto_coe

theorem _root_.continuous_coe_real_ereal : Continuous ((↑) : ℝ → EReal) :=
  embedding_coe.continuous
#align continuous_coe_real_ereal continuous_coe_real_ereal

theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe.continuous_iff.symm
#align ereal.continuous_coe_iff EReal.continuous_coe_iff

theorem nhds_coe {r : ℝ} : 𝓝 (r : EReal) = (𝓝 r).map (↑) :=
  (openEmbedding_coe.map_nhds_eq r).symm
#align ereal.nhds_coe EReal.nhds_coe

theorem nhds_coe_coe {r p : ℝ} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (↑p.1, ↑p.2) :=
  ((openEmbedding_coe.prod openEmbedding_coe).map_nhds_eq (r, p)).symm
#align ereal.nhds_coe_coe EReal.nhds_coe_coe

theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) := by
  lift a to ℝ using ⟨ha, h'a⟩
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
#align ereal.tendsto_to_real EReal.tendsto_toReal

theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))
#align ereal.continuous_on_to_real EReal.continuousOn_toReal

/-- The set of finite `EReal` numbers is homeomorphic to `ℝ`. -/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ where
  toEquiv := neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_restrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _
#align ereal.ne_bot_top_homeomorph_real EReal.neBotTopHomeomorphReal

/-! ### ennreal coercion -/

theorem embedding_coe_ennreal : Embedding ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.embedding_of_ordConnected <| by
    rw [range_coe_ennreal]; exact ordConnected_Ici
#align ereal.embedding_coe_ennreal EReal.embedding_coe_ennreal

theorem closedEmbedding_coe_ennreal : ClosedEmbedding ((↑) : ℝ≥0∞ → EReal) :=
  ⟨embedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]
theorem tendsto_coe_ennreal {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe_ennreal.tendsto_nhds_iff.symm
#align ereal.tendsto_coe_ennreal EReal.tendsto_coe_ennreal

theorem _root_.continuous_coe_ennreal_ereal : Continuous ((↑) : ℝ≥0∞ → EReal) :=
  embedding_coe_ennreal.continuous
#align continuous_coe_ennreal_ereal continuous_coe_ennreal_ereal

theorem continuous_coe_ennreal_iff {f : α → ℝ≥0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  embedding_coe_ennreal.continuous_iff.symm
#align ereal.continuous_coe_ennreal_iff EReal.continuous_coe_ennreal_iff

/-! ### Neighborhoods of infinity -/

theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp only [lt_top_iff_ne_top]
#align ereal.nhds_top EReal.nhds_top

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Ioi ·) := by
  refine nhds_top_basis.to_hasBasis (fun x hx => ?_) fun _ _ ↦ ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, hxy, -⟩
  exact ⟨_, trivial, Ioi_subset_Ioi hxy.le⟩

theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi ↑a) := nhds_top_basis.eq_iInf
#align ereal.nhds_top' EReal.nhds_top'

theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s :=
  nhds_top_basis.mem_iff.trans <| by simp only [true_and]
#align ereal.mem_nhds_top_iff EReal.mem_nhds_top_iff

theorem tendsto_nhds_top_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
  nhds_top_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Ioi]
#align ereal.tendsto_nhds_top_iff_real EReal.tendsto_nhds_top_iff_real

theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]
#align ereal.nhds_bot EReal.nhds_bot

theorem nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Iio ·) := by
  refine nhds_bot_basis.to_hasBasis (fun x hx => ?_) fun _ _ ↦ ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩

theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : ℝ, 𝓟 (Iio ↑a) :=
  nhds_bot_basis.eq_iInf
#align ereal.nhds_bot' EReal.nhds_bot'

theorem mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 (⊥ : EReal) ↔ ∃ y : ℝ, Iio (y : EReal) ⊆ s :=
  nhds_bot_basis.mem_iff.trans <| by simp only [true_and]
#align ereal.mem_nhds_bot_iff EReal.mem_nhds_bot_iff

theorem tendsto_nhds_bot_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x :=
  nhds_bot_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Iio]
#align ereal.tendsto_nhds_bot_iff_real EReal.tendsto_nhds_bot_iff_real

/-! ### Liminfs and Limsups -/

/- The theorem `Filter.liminf_le_liminf` uses two hypotheses (that some sequences are bounded
under/above). These two hypotheses are always satisfied in EReal.
This specialization avoids them. -/
theorem liminf_le_liminf {α : Type*} {f : Filter α} {u v : α → EReal} (h : u ≤ᶠ[f] v) :
    liminf u f ≤ liminf v f := Filter.liminf_le_liminf h

/- The theorem `Filter.limsup_le_limsup` uses two hypotheses (that some sequences are bounded
under/above). These two hypotheses are always satisfied in EReal.
This specialization avoids them. -/
theorem limsup_le_limsup {α : Type*} {f : Filter α} {u v : α → EReal} (h : u ≤ᶠ[f] v) :
    limsup u f ≤ limsup v f := Filter.limsup_le_limsup h

theorem limsup_add_le_lt₂ {α : Type*} {f : Filter α} {u v : α → EReal} {a b : EReal}
    (ha : limsup u f < a) (hb : limsup v f < b) : limsup (u + v) f ≤ a + b := by
  rcases eq_or_neBot f with (rfl | _); simp only [limsup_bot, bot_le]
  rw [← @limsup_const EReal α _ f _ (a+b)]
  apply limsup_le_limsup (Eventually.mp (Eventually.and (eventually_lt_of_limsup_lt ha)
    (eventually_lt_of_limsup_lt hb)) (eventually_of_forall _))
  simp only [Pi.add_apply, and_imp]
  intro x
  exact fun ux_lt_a vx_lt_b ↦ add_le_add (le_of_lt ux_lt_a) (le_of_lt vx_lt_b)

/-
TODO: Since `EReal.le_iff_le_forall_real_gt` is ported in `Mathlib.Data.Real.EReal`
via the PR `#14125`, we need to:
-- Wait for PR `#14125` to be merged
-- Rebase to master
-- Uncomment this theorem
-- Consider changing its name to `limsup_add_bot_of_ne_top` to stick to naming conventions

theorem limsup_add_bot_ne_top {α : Type _} {f : Filter α} {u : α → EReal} {v : α → EReal}
    (h : limsup u f = ⊥) (h' : limsup v f ≠ ⊤) :
    limsup (u+v) f = ⊥ := by
  apply le_bot_iff.1
  apply (EReal.le_iff_le_forall_real_gt ⊥ (limsup (u+v) f)).2
  intro x
  rcases EReal.exists_between_coe_real (Ne.lt_top h') with ⟨y, ⟨hy, _⟩⟩
  intro trash; clear trash
  rw [← sub_add_cancel x y, EReal.coe_add (x-y) y, EReal.coe_sub x y]
  apply @EReal.limsup_add_le_lt₂ α f u v (x-y) y _ hy
  rw [h, ← EReal.coe_sub x y]
  exact EReal.bot_lt_coe (x-y)
-/

/-
TODO: Since `limsup_add_bot_ne_top` above is dependent from a lemma ported in
`Mathlib.Data.Real.EReal` via the PR #14125, we need to:
-- Wait for PR #14125 to be merged
-- Rebase to master
-- Uncomment this theorem

theorem limsup_add_le_add_limsup {α : Type _} {f : Filter α} {u v : α → EReal}
    (h : limsup u f ≠ ⊥ ∨ limsup v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ limsup v f ≠ ⊥) :
    limsup (u + v) f ≤ (limsup u f) + (limsup v f) := by
  /- WLOG, ⊥ < limsup u f. -/
  rcases eq_bot_or_bot_lt (limsup u f) with (u_bot | u_nbot)
  · rcases h with (u_nbot | v_ntop)
    · exfalso; exact u_nbot u_bot
    · rw [EReal.limsup_add_bot_ne_top u_bot v_ntop]; exact bot_le
  /- WLOG, ⊥ < limsup v f. -/
  rcases eq_bot_or_bot_lt (limsup v f) with (v_bot | v_nbot)
  · rcases h' with (u_ntop | v_nbot)
    · rw [add_comm, EReal.limsup_add_bot_ne_top v_bot u_ntop]; exact bot_le
    · exfalso; exact v_nbot v_bot
  clear h h'
  /- WLOG, limsup v f < ⊤. -/
  rcases eq_top_or_lt_top (limsup v f) with (v_top | v_ntop)
  · rw [v_top, EReal.ne_bot_add_top (ne_of_gt u_nbot)]; exact le_top
  /- General case. -/
  have limsup_v_real := EReal.coe_toReal (ne_of_lt v_ntop) (ne_of_gt v_nbot)
  apply (EReal.le_iff_le_forall_real_gt _ _).2
  intros x hx
  rcases EReal.lt_iff_exists_real_btwn.1 hx with ⟨y, ⟨sum_lt_y, y_lt_x⟩⟩; clear hx
  have key₁ : limsup u f < (y - limsup v f) := by
    apply lt_of_eq_of_lt _ (EReal.sub_lt_sub_of_lt_of_le sum_lt_y (le_of_eq (Eq.refl (limsup v f)))
      (ne_of_gt v_nbot) (ne_of_lt v_ntop))
    rw [← limsup_v_real, add_sub_cancel_right]
  have key₂ : limsup v f < limsup v f + x - y := by
    rw [← limsup_v_real]; norm_cast; norm_cast at y_lt_x; linarith
  apply le_of_le_of_eq (EReal.limsup_add_le_lt₂ key₁ key₂); clear key₁ key₂ y_lt_x sum_lt_y
  rw [← limsup_v_real]; norm_cast; linarith
-/

theorem ge_iff_le_forall_real_lt (x y : EReal) : y ≤ x ↔ ∀ (z : ℝ), (z < y) → (z ≤ x) := by
  constructor
  · intros h z z_lt_y
    exact le_trans (le_of_lt z_lt_y) h
  · intro h
    induction' x using EReal.rec with x
    · apply le_of_eq
      apply (eq_bot_iff_forall_lt y).2
      intro z
      apply lt_of_not_le
      intro z_le_y
      apply not_le_of_lt (bot_lt_coe (z-1))
      specialize h (z-1)
      apply h (lt_of_lt_of_le _ z_le_y)
      norm_cast
      exact sub_one_lt z
    · induction' y using EReal.rec with y
      · exact bot_le
      · norm_cast
        norm_cast at h
        by_contra x_lt_y
        rcases exists_between (lt_of_not_le x_lt_y) with ⟨z, ⟨x_lt_z, z_lt_y⟩⟩
        specialize h z z_lt_y
        exact not_le_of_lt x_lt_z h
      · exfalso
        specialize h (x + 1) (coe_lt_top (x+1))
        norm_cast at h
        exact not_le_of_lt (lt_add_one x) h
    · exact le_top

lemma liminf_add_ge_gt₂ {α : Type _} {f : Filter α} {u v : α → EReal} {a b : EReal}
    (ha : a < liminf u f) (hb : b < liminf v f) :
    a + b ≤ liminf (u + v) f := by
  rcases eq_or_neBot f with (rfl | _); simp only [liminf_bot, le_top]
  rw [← @liminf_const EReal α _ f _ (a+b)]
  apply liminf_le_liminf
  apply Eventually.mp (Eventually.and
    (eventually_lt_of_lt_liminf ha) (eventually_lt_of_lt_liminf hb))
  apply eventually_of_forall
  intros x
  simp only [Pi.add_apply, and_imp]
  exact fun ux_lt_a vx_lt_b ↦ add_le_add (le_of_lt ux_lt_a) (le_of_lt vx_lt_b)

lemma liminf_add_top_ne_bot {α : Type _} {f : Filter α} {u : α → EReal} {v : α → EReal}
    (h : liminf u f = ⊤) (h' : liminf v f ≠ ⊥) :
    liminf (u + v) f = ⊤ := by
  apply top_le_iff.1
  apply (EReal.ge_iff_le_forall_real_lt (liminf (u+v) f) ⊤).2
  intro x
  rcases EReal.exists_between_coe_real (Ne.bot_lt h') with ⟨y, ⟨_, hy⟩⟩
  intro trash; clear trash
  rw [← sub_add_cancel x y, EReal.coe_add (x-y) y, EReal.coe_sub x y]
  apply @EReal.liminf_add_ge_gt₂ α f u v (x-y) y _ hy
  rw [h, ← EReal.coe_sub x y]
  exact EReal.coe_lt_top (x-y)

theorem add_liminf_le_liminf_add {α : Type _} {f : Filter α} {u v : α → EReal}
    (h : liminf u f ≠ ⊥ ∨ liminf v f ≠ ⊤) (h' : liminf u f ≠ ⊤ ∨ liminf v f ≠ ⊥) :
    (liminf u f) + (liminf v f) ≤ liminf (u + v) f:= by
  /- WLOG, liminf v f < ⊤. -/
  rcases eq_top_or_lt_top (liminf v f) with (v_top | v_ntop)
  · rcases h with (u_nbot | v_ntop)
    · rw [add_comm u v, EReal.liminf_add_top_ne_bot v_top u_nbot]; exact le_top
    · exfalso; exact v_ntop v_top
  clear h h'
  /- WLOG, ⊥ < liminf v f. -/
  rcases eq_bot_or_bot_lt (liminf v f) with (v_bot | v_nbot)
  · rw [v_bot, EReal.add_bot]; exact bot_le
  /- General case. -/
  have liminf_v_real := EReal.coe_toReal (ne_of_lt v_ntop) (ne_of_gt v_nbot)
  apply (EReal.ge_iff_le_forall_real_lt _ _).2
  intros x hx
  rcases EReal.lt_iff_exists_real_btwn.1 hx with ⟨y, ⟨x_lt_y, y_lt_sum⟩⟩; clear hx
  have key₁ : (y - liminf v f) < liminf u f := by
    apply lt_of_lt_of_eq (EReal.sub_lt_sub_of_lt_of_le y_lt_sum (le_of_eq (Eq.refl (liminf v f)))
      (ne_of_gt v_nbot) (ne_of_lt v_ntop))
    rw [← liminf_v_real, add_sub_cancel_right] -- Wait for the PR
  have key₂ : liminf v f + x - y < liminf v f := by
    rw [← liminf_v_real]
    norm_cast
    norm_cast at x_lt_y
    linarith
  apply le_of_eq_of_le _ (EReal.liminf_add_ge_gt₂ key₁ key₂); clear key₁ key₂ x_lt_y y_lt_sum
  rw [← liminf_v_real]
  norm_cast
  linarith

theorem limsup_le_iff {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal} :
    limsup u f ≤ b ↔ ∀ c : ℝ, b < c → ∀ᶠ a : α in f, u a ≤ c := by
  rw [EReal.le_iff_le_forall_real_gt] -- Wait for the PR
  constructor
  · intro h c b_lt_c
    rcases EReal.exists_between_coe_real b_lt_c with ⟨d, b_lt_d, d_lt_c⟩
    specialize h d b_lt_d
    have key := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt h d_lt_c)
    apply Filter.mem_of_superset key
    simp only [Set.setOf_subset_setOf]
    exact fun a h' ↦ le_of_lt h'
  · intro h c b_lt_c
    rcases eq_or_neBot f with (rfl | _)
    · simp only [limsup_bot, bot_le]
    · specialize h c b_lt_c
      rw [← @Filter.limsup_const EReal α _ f _ (c : EReal)]
      exact limsup_le_limsup h

theorem limsup_le_const_forall {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal}
    (h : ∀ a : α, u a ≤ b) :
    limsup u f ≤ b := by
  apply EReal.limsup_le_iff.2
  exact fun c b_lt_c ↦ eventually_of_forall (fun a : α ↦ le_trans (h a) (le_of_lt b_lt_c))

theorem const_le_limsup_forall {α : Type _} {f : Filter α} [NeBot f] {u : α → EReal}
    {b : EReal} (h : ∀ a : α, b ≤ u a) :
    b ≤ limsup u f := by
  rw [← @Filter.limsup_const EReal α _ f _ b]
  exact limsup_le_limsup (eventually_of_forall h)

theorem liminf_le_const_forall {α : Type _} {f : Filter α} [NeBot f] {u : α → EReal}
    {b : EReal} (h : ∀ a : α, u a ≤ b) :
    liminf u f ≤ b := by
  rw [← @Filter.liminf_const EReal α _ f _ b]
  exact liminf_le_liminf (eventually_of_forall h)

theorem const_le_liminf_forall {α : Type _} {f : Filter α} {u : α → EReal} {b : EReal}
    (h : ∀ a : α, b ≤ u a) :
    b ≤ liminf u f := by
  rcases eq_or_neBot f with (rfl | _)
  · simp only [liminf_bot, le_top]
  · rw [← @Filter.liminf_const EReal α _ f _ b]
    exact liminf_le_liminf (eventually_of_forall h)

theorem limsup_max {α : Type _} {f : Filter α} {u v : α → EReal} :
    limsup (fun a ↦ max (u a) (v a)) f = max (limsup u f) (limsup v f) := by
  rcases eq_or_neBot f with (rfl | _); simp [limsup_bot]
  apply le_antisymm
  · apply EReal.limsup_le_iff.2
    intro b hb
    have hu := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_left _ _) hb)
    have hv := Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt (le_max_right _ _) hb); clear hb
    apply Filter.mem_of_superset (Filter.inter_mem hu hv); clear hu hv
    intro a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, max_le_iff, and_imp]
    exact fun hua hva ↦ ⟨le_of_lt hua, le_of_lt hva⟩
  · apply max_le
    · exact limsup_le_limsup (eventually_of_forall (fun a : α ↦ le_max_left (u a) (v a)))
    · exact limsup_le_limsup (eventually_of_forall (fun a : α ↦ le_max_right (u a) (v a)))

/-! ### Continuity of addition -/

theorem continuousAt_add_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (· ∘ ·), tendsto_coe,
    tendsto_add]
#align ereal.continuous_at_add_coe_coe EReal.continuousAt_add_coe_coe

theorem continuousAt_add_top_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, sub_add_cancel] using add_lt_add h.1 h.2
#align ereal.continuous_at_add_top_coe EReal.continuousAt_add_top_coe

theorem continuousAt_add_coe_top (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) := by
  simpa only [add_comm, (· ∘ ·), ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))
#align ereal.continuous_at_add_coe_top EReal.continuousAt_add_coe_top

theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2
#align ereal.continuous_at_add_top_top EReal.continuousAt_add_top_top

theorem continuousAt_add_bot_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, sub_add_cancel] using add_lt_add h.1 h.2
#align ereal.continuous_at_add_bot_coe EReal.continuousAt_add_bot_coe

theorem continuousAt_add_coe_bot (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) := by
  simpa only [add_comm, (· ∘ ·), ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))
#align ereal.continuous_at_add_coe_bot EReal.continuousAt_add_coe_bot

theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2
#align ereal.continuous_at_add_bot_bot EReal.continuousAt_add_bot_bot

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
#align ereal.continuous_at_add EReal.continuousAt_add

/-! ### Negation -/

instance : ContinuousNeg EReal := ⟨negOrderIso.continuous⟩

/-- Negation on `EReal` as a homeomorphism -/
@[deprecated Homeomorph.neg (since := "2023-03-14")]
def negHomeo : EReal ≃ₜ EReal :=
  negOrderIso.toHomeomorph
#align ereal.neg_homeo EReal.negHomeo

@[deprecated continuous_neg (since := "2023-03-14")]
protected theorem continuous_neg : Continuous fun x : EReal => -x :=
  continuous_neg
#align ereal.continuous_neg EReal.continuous_neg

end EReal
