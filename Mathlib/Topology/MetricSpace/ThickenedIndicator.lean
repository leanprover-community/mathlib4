/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Data.Real.ENNReal
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Order.Filter.IndicatorFunction

#align_import topology.metric_space.thickened_indicator from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Thickened indicators

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

 * `thickenedIndicatorAux δ E`: The `δ`-thickened indicator of a set `E` as an
   unbundled `ℝ≥0∞`-valued function.
 * `thickenedIndicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
   bounded continuous `ℝ≥0`-valued function.

## Main results

 * For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
   pointwise to the indicator of `closure E`.
   - `thickenedIndicatorAux_tendsto_indicator_closure`: The version is for the
     unbundled `ℝ≥0∞`-valued functions.
   - `thickenedIndicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
     bounded continuous functions.

-/


open Classical NNReal ENNReal Topology BoundedContinuousFunction

open NNReal ENNReal Set Metric EMetric Filter

noncomputable section thickenedIndicator

variable {α : Type*} [PseudoEMetricSpace α]

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEdist _ E`.

`thickenedIndicatorAux` is the unbundled `ℝ≥0∞`-valued function. See `thickenedIndicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values. -/
def thickenedIndicatorAux (δ : ℝ) (E : Set α) : α → ℝ≥0∞ :=
  fun x : α => (1 : ℝ≥0∞) - infEdist x E / ENNReal.ofReal δ
#align thickened_indicator_aux thickenedIndicatorAux

theorem continuous_thickenedIndicatorAux {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) := by
  unfold thickenedIndicatorAux
  -- ⊢ Continuous fun x => 1 - infEdist x E / ENNReal.ofReal δ
  let f := fun x : α => (⟨1, infEdist x E / ENNReal.ofReal δ⟩ : ℝ≥0 × ℝ≥0∞)
  -- ⊢ Continuous fun x => 1 - infEdist x E / ENNReal.ofReal δ
  let sub := fun p : ℝ≥0 × ℝ≥0∞ => (p.1 : ℝ≥0∞) - p.2
  -- ⊢ Continuous fun x => 1 - infEdist x E / ENNReal.ofReal δ
  rw [show (fun x : α => (1 : ℝ≥0∞) - infEdist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  -- ⊢ Continuous (sub ∘ f)
  apply (@ENNReal.continuous_nnreal_sub 1).comp
  -- ⊢ Continuous fun x => (f x).snd
  apply (ENNReal.continuous_div_const (ENNReal.ofReal δ) _).comp continuous_infEdist
  -- ⊢ ENNReal.ofReal δ ≠ 0
  norm_num [δ_pos]
  -- 🎉 no goals
#align continuous_thickened_indicator_aux continuous_thickenedIndicatorAux

theorem thickenedIndicatorAux_le_one (δ : ℝ) (E : Set α) (x : α) :
    thickenedIndicatorAux δ E x ≤ 1 := by
  apply @tsub_le_self _ _ _ _ (1 : ℝ≥0∞)
  -- 🎉 no goals
#align thickened_indicator_aux_le_one thickenedIndicatorAux_le_one

theorem thickenedIndicatorAux_lt_top {δ : ℝ} {E : Set α} {x : α} :
    thickenedIndicatorAux δ E x < ∞ :=
  lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top
#align thickened_indicator_aux_lt_top thickenedIndicatorAux_lt_top

theorem thickenedIndicatorAux_closure_eq (δ : ℝ) (E : Set α) :
    thickenedIndicatorAux δ (closure E) = thickenedIndicatorAux δ E := by
  simp_rw [thickenedIndicatorAux, infEdist_closure]
  -- 🎉 no goals
#align thickened_indicator_aux_closure_eq thickenedIndicatorAux_closure_eq

theorem thickenedIndicatorAux_one (δ : ℝ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicatorAux δ E x = 1 := by
  simp [thickenedIndicatorAux, infEdist_zero_of_mem x_in_E, tsub_zero]
  -- 🎉 no goals
#align thickened_indicator_aux_one thickenedIndicatorAux_one

theorem thickenedIndicatorAux_one_of_mem_closure (δ : ℝ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicatorAux δ E x = 1 := by
  rw [← thickenedIndicatorAux_closure_eq, thickenedIndicatorAux_one δ (closure E) x_mem]
  -- 🎉 no goals
#align thickened_indicator_aux_one_of_mem_closure thickenedIndicatorAux_one_of_mem_closure

theorem thickenedIndicatorAux_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicatorAux δ E x = 0 := by
  rw [thickening, mem_setOf_eq, not_lt] at x_out
  -- ⊢ thickenedIndicatorAux δ E x = 0
  unfold thickenedIndicatorAux
  -- ⊢ 1 - infEdist x E / ENNReal.ofReal δ = 0
  apply le_antisymm _ bot_le
  -- ⊢ 1 - infEdist x E / ENNReal.ofReal δ ≤ ⊥
  have key := tsub_le_tsub
    (@rfl _ (1 : ℝ≥0∞)).le (ENNReal.div_le_div x_out (@rfl _ (ENNReal.ofReal δ : ℝ≥0∞)).le)
  rw [ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.mpr δ_pos)) ofReal_ne_top] at key
  -- ⊢ 1 - infEdist x E / ENNReal.ofReal δ ≤ ⊥
  simpa using key
  -- 🎉 no goals
#align thickened_indicator_aux_zero thickenedIndicatorAux_zero

theorem thickenedIndicatorAux_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickenedIndicatorAux δ₁ E ≤ thickenedIndicatorAux δ₂ E :=
  fun _ => tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))
#align thickened_indicator_aux_mono thickenedIndicatorAux_mono

theorem indicator_le_thickenedIndicatorAux (δ : ℝ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ thickenedIndicatorAux δ E := by
  intro a
  -- ⊢ indicator E (fun x => 1) a ≤ thickenedIndicatorAux δ E a
  by_cases a ∈ E
  -- ⊢ indicator E (fun x => 1) a ≤ thickenedIndicatorAux δ E a
  -- ⊢ indicator E (fun x => 1) a ≤ thickenedIndicatorAux δ E a
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
    -- 🎉 no goals
  · simp only [h, indicator_of_not_mem, not_false_iff, zero_le]
    -- 🎉 no goals
#align indicator_le_thickened_indicator_aux indicator_le_thickenedIndicatorAux

theorem thickenedIndicatorAux_subset (δ : ℝ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    thickenedIndicatorAux δ E₁ ≤ thickenedIndicatorAux δ E₂ :=
  fun _ => tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div (infEdist_anti subset) rfl.le)
#align thickened_indicator_aux_subset thickenedIndicatorAux_subset

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise (i.e., w.r.t. the product topology on `α → ℝ≥0∞`) to the indicator function of the
closure of E.

This statement is for the unbundled `ℝ≥0∞`-valued functions `thickenedIndicatorAux δ E`, see
`thickenedIndicator_tendsto_indicator_closure` for the version for bundled `ℝ≥0`-valued
bounded continuous functions. -/
theorem thickenedIndicatorAux_tendsto_indicator_closure {δseq : ℕ → ℝ}
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n => thickenedIndicatorAux (δseq n) E) atTop
      (𝓝 (indicator (closure E) fun _ => (1 : ℝ≥0∞))) := by
  rw [tendsto_pi_nhds]
  -- ⊢ ∀ (x : α), Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 (i …
  intro x
  -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 (indicator (c …
  by_cases x_mem_closure : x ∈ closure E
  -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 (indicator (c …
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    -- ⊢ Tendsto (fun i => 1) atTop (𝓝 (indicator (closure E) (fun x => 1) x))
    rw [show (indicator (closure E) fun _ => (1 : ℝ≥0∞)) x = 1 by
        simp only [x_mem_closure, indicator_of_mem]]
    exact tendsto_const_nhds
    -- 🎉 no goals
  · rw [show (closure E).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 by
        simp only [x_mem_closure, indicator_of_not_mem, not_false_iff]]
    rcases exists_real_pos_lt_infEdist_of_not_mem_closure x_mem_closure with ⟨ε, ⟨ε_pos, ε_lt⟩⟩
    -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 0)
    rw [Metric.tendsto_nhds] at δseq_lim
    -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 0)
    specialize δseq_lim ε ε_pos
    -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 0)
    simp only [dist_zero_right, Real.norm_eq_abs, eventually_atTop, ge_iff_le] at δseq_lim
    -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 0)
    rcases δseq_lim with ⟨N, hN⟩
    -- ⊢ Tendsto (fun i => thickenedIndicatorAux (δseq i) E x) atTop (𝓝 0)
    apply @tendsto_atTop_of_eventually_const _ _ _ _ _ _ _ N
    -- ⊢ ∀ (i : ℕ), i ≥ N → thickenedIndicatorAux (δseq i) E x = 0
    intro n n_large
    -- ⊢ thickenedIndicatorAux (δseq n) E x = 0
    have key : x ∉ thickening ε E := by simpa only [thickening, mem_setOf_eq, not_lt] using ε_lt.le
    -- ⊢ thickenedIndicatorAux (δseq n) E x = 0
    refine' le_antisymm _ bot_le
    -- ⊢ thickenedIndicatorAux (δseq n) E x ≤ 0
    apply (thickenedIndicatorAux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans
    -- ⊢ thickenedIndicatorAux ε E x ≤ 0
    exact (thickenedIndicatorAux_zero ε_pos E key).le
    -- 🎉 no goals
#align thickened_indicator_aux_tendsto_indicator_closure thickenedIndicatorAux_tendsto_indicator_closure

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEdist _ E`.

`thickenedIndicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickenedIndicatorAux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps]
def thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : α →ᵇ ℝ≥0 where
  toFun := fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous continuousOn_toNNReal
      (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    -- ⊢ thickenedIndicatorAux δ E x ∈ {a | a ≠ ⊤}
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).ne
    -- 🎉 no goals
  map_bounded' := by
    use 2
    -- ⊢ ∀ (x y : α), dist (ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.to …
    intro x y
    -- ⊢ dist (ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thick …
    rw [NNReal.dist_eq]
    -- ⊢ |↑(ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickene …
    apply (abs_sub _ _).trans
    -- ⊢ |↑(ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickene …
    rw [NNReal.abs_eq, NNReal.abs_eq, ← one_add_one_eq_two]
    -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickened …
    have key := @thickenedIndicatorAux_le_one _ _ δ E
    -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickened …
    apply add_le_add <;>
    -- ⊢ ↑(ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickened …
      · norm_cast
        -- ⊢ ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickenedIn …
        -- ⊢ ContinuousMap.toFun (ContinuousMap.mk fun x => ENNReal.toNNReal (thickenedIn …
        -- 🎉 no goals
        refine' (toNNReal_le_toNNReal (lt_of_le_of_lt (key _) one_lt_top).ne one_ne_top).mpr (key _)
        -- 🎉 no goals
#align thickened_indicator thickenedIndicator

theorem thickenedIndicator.coeFn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    ⇑(thickenedIndicator δ_pos E) = ENNReal.toNNReal ∘ thickenedIndicatorAux δ E :=
  rfl
#align thickened_indicator.coe_fn_eq_comp thickenedIndicator.coeFn_eq_comp

theorem thickenedIndicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α) :
    thickenedIndicator δ_pos E x ≤ 1 := by
  rw [thickenedIndicator.coeFn_eq_comp]
  -- ⊢ (ENNReal.toNNReal ∘ thickenedIndicatorAux δ E) x ≤ 1
  simpa using (toNNReal_le_toNNReal thickenedIndicatorAux_lt_top.ne one_ne_top).mpr
    (thickenedIndicatorAux_le_one δ E x)
#align thickened_indicator_le_one thickenedIndicator_le_one

theorem thickenedIndicator_one_of_mem_closure {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicator δ_pos E x = 1 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_one_of_mem_closure δ E x_mem, one_toNNReal]
  -- 🎉 no goals
#align thickened_indicator_one_of_mem_closure thickenedIndicator_one_of_mem_closure

theorem thickenedIndicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicator δ_pos E x = 1 :=
  thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)
#align thickened_indicator_one thickenedIndicator_one

theorem thickenedIndicator_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicator δ_pos E x = 0 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_zero δ_pos E x_out, zero_toNNReal]
  -- 🎉 no goals
#align thickened_indicator_zero thickenedIndicator_zero

theorem indicator_le_thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0)) ≤ thickenedIndicator δ_pos E := by
  intro a
  -- ⊢ indicator E (fun x => 1) a ≤ ↑(thickenedIndicator δ_pos E) a
  by_cases a ∈ E
  -- ⊢ indicator E (fun x => 1) a ≤ ↑(thickenedIndicator δ_pos E) a
  -- ⊢ indicator E (fun x => 1) a ≤ ↑(thickenedIndicator δ_pos E) a
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
    -- 🎉 no goals
  · simp only [h, indicator_of_not_mem, not_false_iff, zero_le]
    -- 🎉 no goals
#align indicator_le_thickened_indicator indicator_le_thickenedIndicator

theorem thickenedIndicator_mono {δ₁ δ₂ : ℝ} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂)
    (E : Set α) : ⇑(thickenedIndicator δ₁_pos E) ≤ thickenedIndicator δ₂_pos E := by
  intro x
  -- ⊢ ↑(thickenedIndicator δ₁_pos E) x ≤ ↑(thickenedIndicator δ₂_pos E) x
  apply (toNNReal_le_toNNReal thickenedIndicatorAux_lt_top.ne thickenedIndicatorAux_lt_top.ne).mpr
  -- ⊢ thickenedIndicatorAux δ₁ E x ≤ thickenedIndicatorAux δ₂ E x
  apply thickenedIndicatorAux_mono hle
  -- 🎉 no goals
#align thickened_indicator_mono thickenedIndicator_mono

theorem thickenedIndicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    ⇑(thickenedIndicator δ_pos E₁) ≤ thickenedIndicator δ_pos E₂ := fun x =>
  (toNNReal_le_toNNReal thickenedIndicatorAux_lt_top.ne thickenedIndicatorAux_lt_top.ne).mpr
    (thickenedIndicatorAux_subset δ subset x)
#align thickened_indicator_subset thickenedIndicator_subset

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise to the indicator function of the closure of E.

Note: This version is for the bundled bounded continuous functions, but the topology is not
the topology on `α →ᵇ ℝ≥0`. Coercions to functions `α → ℝ≥0` are done first, so the topology
instance is the product topology (the topology of pointwise convergence). -/
theorem thickenedIndicator_tendsto_indicator_closure {δseq : ℕ → ℝ} (δseq_pos : ∀ n, 0 < δseq n)
    (δseq_lim : Tendsto δseq atTop (𝓝 0)) (E : Set α) :
    Tendsto (fun n : ℕ => ((↑) : (α →ᵇ ℝ≥0) → α → ℝ≥0) (thickenedIndicator (δseq_pos n) E)) atTop
      (𝓝 (indicator (closure E) fun _ => (1 : ℝ≥0))) := by
  have key := thickenedIndicatorAux_tendsto_indicator_closure δseq_lim E
  -- ⊢ Tendsto (fun n => ↑(thickenedIndicator (_ : 0 < δseq n) E)) atTop (𝓝 (indica …
  rw [tendsto_pi_nhds] at *
  -- ⊢ ∀ (x : α), Tendsto (fun i => ↑(thickenedIndicator (_ : 0 < δseq i) E) x) atT …
  intro x
  -- ⊢ Tendsto (fun i => ↑(thickenedIndicator (_ : 0 < δseq i) E) x) atTop (𝓝 (indi …
  rw [show indicator (closure E) (fun _ => (1 : ℝ≥0)) x =
        (indicator (closure E) (fun _ => (1 : ℝ≥0∞)) x).toNNReal
      by refine' (congr_fun (comp_indicator_const 1 ENNReal.toNNReal zero_toNNReal) x).symm]
  refine' Tendsto.comp (tendsto_toNNReal _) (key x)
  -- ⊢ indicator (closure E) (fun x => 1) x ≠ ⊤
  by_cases x_mem : x ∈ closure E <;> simp [x_mem]
  -- ⊢ indicator (closure E) (fun x => 1) x ≠ ⊤
                                     -- 🎉 no goals
                                     -- 🎉 no goals
#align thickened_indicator_tendsto_indicator_closure thickenedIndicator_tendsto_indicator_closure

end thickenedIndicator

section indicator

variable {α : Type*} [PseudoEMetricSpace α] {β : Type*} [One β]

/-- Pointwise, the multiplicative indicators of δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ>0 tends to zero. -/
@[to_additive "Pointwise, the indicators of δ-thickenings of a set eventually coincide
with the indicator of the set as δ>0 tends to zero."]
lemma mulIndicator_thickening_eventually_eq_mulIndicator_closure (f : α → β) (E : Set α) (x : α) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (Metric.thickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x ∈ closure E
  -- ⊢ ∀ᶠ (δ : ℝ) in 𝓝[Ioi 0] 0, mulIndicator (thickening δ E) f x = mulIndicator ( …
  · filter_upwards [self_mem_nhdsWithin] with δ δ_pos
    -- ⊢ mulIndicator (thickening δ E) f x = mulIndicator (closure E) f x
    simp only [closure_subset_thickening δ_pos E x_mem_closure, mulIndicator_of_mem, x_mem_closure]
    -- 🎉 no goals
  · have obs := eventually_not_mem_thickening_of_infEdist_pos x_mem_closure
    -- ⊢ ∀ᶠ (δ : ℝ) in 𝓝[Ioi 0] 0, mulIndicator (thickening δ E) f x = mulIndicator ( …
    filter_upwards [mem_nhdsWithin_of_mem_nhds obs, self_mem_nhdsWithin]
      with δ x_notin_thE _
    simp only [x_notin_thE, not_false_eq_true, mulIndicator_of_not_mem, x_mem_closure]
    -- 🎉 no goals

/-- Pointwise, the multiplicative indicators of closed δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ tends to zero. -/
@[to_additive "Pointwise, the indicators of closed δ-thickenings of a set eventually coincide
with the indicator of the set as δ tends to zero."]
lemma mulIndicator_cthickening_eventually_eq_mulIndicator_closure (f : α → β) (E : Set α) (x : α) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (Metric.cthickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x ∈ closure E
  -- ⊢ ∀ᶠ (δ : ℝ) in 𝓝 0, mulIndicator (cthickening δ E) f x = mulIndicator (closur …
  · filter_upwards [univ_mem] with δ _
    -- ⊢ mulIndicator (cthickening δ E) f x = mulIndicator (closure E) f x
    have obs : x ∈ cthickening δ E := closure_subset_cthickening δ E x_mem_closure
    -- ⊢ mulIndicator (cthickening δ E) f x = mulIndicator (closure E) f x
    rw [mulIndicator_of_mem obs f, mulIndicator_of_mem x_mem_closure f]
    -- 🎉 no goals
  · filter_upwards [eventually_not_mem_cthickening_of_infEdist_pos x_mem_closure] with δ hδ
    -- ⊢ mulIndicator (cthickening δ E) f x = mulIndicator (closure E) f x
    simp only [hδ, not_false_eq_true, mulIndicator_of_not_mem, x_mem_closure]
    -- 🎉 no goals

variable [TopologicalSpace β]

/-- The multiplicative indicators of δ-thickenings of a set tend pointwise to the multiplicative
indicator of the set, as δ>0 tends to zero. -/
@[to_additive "The indicators of δ-thickenings of a set tend pointwise to the indicator of the
set, as δ>0 tends to zero."]
lemma tendsto_mulIndicator_thickening_mulIndicator_closure (f : α → β) (E : Set α) :
    Tendsto (fun δ ↦ (Metric.thickening δ E).mulIndicator f) (𝓝[>] 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  -- ⊢ ∀ (x : α), Tendsto (fun i => mulIndicator (thickening i E) f x) (𝓝[Ioi 0] 0) …
  intro x
  -- ⊢ Tendsto (fun i => mulIndicator (thickening i E) f x) (𝓝[Ioi 0] 0) (𝓝 (mulInd …
  rw [tendsto_congr' (mulIndicator_thickening_eventually_eq_mulIndicator_closure f E x)]
  -- ⊢ Tendsto (fun x_1 => mulIndicator (closure E) f x) (𝓝[Ioi 0] 0) (𝓝 (mulIndica …
  apply tendsto_const_nhds
  -- 🎉 no goals

/-- The multiplicative indicators of closed δ-thickenings of a set tend pointwise to the
multiplicative indicator of the set, as δ tends to zero. -/
@[to_additive "The indicators of closed δ-thickenings of a set tend pointwise to the indicator
of the set, as δ tends to zero."]
lemma tendsto_mulIndicator_cthickening_mulIndicator_closure (f : α → β) (E : Set α) :
    Tendsto (fun δ ↦ (Metric.cthickening δ E).mulIndicator f) (𝓝 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  -- ⊢ ∀ (x : α), Tendsto (fun i => mulIndicator (cthickening i E) f x) (𝓝 0) (𝓝 (m …
  intro x
  -- ⊢ Tendsto (fun i => mulIndicator (cthickening i E) f x) (𝓝 0) (𝓝 (mulIndicator …
  rw [tendsto_congr' (mulIndicator_cthickening_eventually_eq_mulIndicator_closure f E x)]
  -- ⊢ Tendsto (fun x_1 => mulIndicator (closure E) f x) (𝓝 0) (𝓝 (mulIndicator (cl …
  apply tendsto_const_nhds
  -- 🎉 no goals

end indicator
