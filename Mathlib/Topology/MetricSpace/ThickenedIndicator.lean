/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Closure
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

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

@[expose] public section

open NNReal ENNReal Topology BoundedContinuousFunction Set Metric Filter

noncomputable section thickenedIndicator

variable {α : Type*} [PseudoEMetricSpace α]

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicatorAux` is the unbundled `ℝ≥0∞`-valued function. See `thickenedIndicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values. -/
def thickenedIndicatorAux (δ : ℝ) (E : Set α) : α → ℝ≥0∞ :=
  fun x : α => (1 : ℝ≥0∞) - infEDist x E / ENNReal.ofReal δ

theorem continuous_thickenedIndicatorAux {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    Continuous (thickenedIndicatorAux δ E) := by
  unfold thickenedIndicatorAux
  let f := fun x : α => (⟨1, infEDist x E / ENNReal.ofReal δ⟩ : ℝ≥0 × ℝ≥0∞)
  let sub := fun p : ℝ≥0 × ℝ≥0∞ => (p.1 : ℝ≥0∞) - p.2
  rw [show (fun x : α => (1 : ℝ≥0∞) - infEDist x E / ENNReal.ofReal δ) = sub ∘ f by rfl]
  apply (@ENNReal.continuous_nnreal_sub 1).comp
  apply (ENNReal.continuous_div_const (ENNReal.ofReal δ) _).comp continuous_infEDist
  norm_num [δ_pos]

theorem thickenedIndicatorAux_le_one (δ : ℝ) (E : Set α) (x : α) :
    thickenedIndicatorAux δ E x ≤ 1 := by
  apply tsub_le_self (α := ℝ≥0∞)

@[aesop safe (rule_sets := [finiteness])]
theorem thickenedIndicatorAux_lt_top {δ : ℝ} {E : Set α} {x : α} :
    thickenedIndicatorAux δ E x < ∞ :=
  lt_of_le_of_lt (thickenedIndicatorAux_le_one _ _ _) one_lt_top

theorem thickenedIndicatorAux_closure_eq (δ : ℝ) (E : Set α) :
    thickenedIndicatorAux δ (closure E) = thickenedIndicatorAux δ E := by
  simp +unfoldPartialApp only [thickenedIndicatorAux, infEDist_closure]

theorem thickenedIndicatorAux_one (δ : ℝ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicatorAux δ E x = 1 := by
  simp [thickenedIndicatorAux, infEDist_zero_of_mem x_in_E, tsub_zero]

theorem thickenedIndicatorAux_one_of_mem_closure (δ : ℝ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicatorAux δ E x = 1 := by
  rw [← thickenedIndicatorAux_closure_eq, thickenedIndicatorAux_one δ (closure E) x_mem]

theorem thickenedIndicatorAux_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicatorAux δ E x = 0 := by
  rw [thickening, mem_setOf_eq, not_lt] at x_out
  unfold thickenedIndicatorAux
  apply le_antisymm _ bot_le
  have key := tsub_le_tsub
    (@rfl _ (1 : ℝ≥0∞)).le (ENNReal.div_le_div x_out (@rfl _ (ENNReal.ofReal δ : ℝ≥0∞)).le)
  rw [ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.mpr δ_pos)) ofReal_ne_top] at key
  simpa [tsub_self] using key

theorem thickenedIndicatorAux_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickenedIndicatorAux δ₁ E ≤ thickenedIndicatorAux δ₂ E :=
  fun _ => tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div rfl.le (ofReal_le_ofReal hle))

theorem indicator_le_thickenedIndicatorAux (δ : ℝ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ thickenedIndicatorAux δ E := by
  intro a
  by_cases h : a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicatorAux_one δ E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

theorem thickenedIndicatorAux_subset (δ : ℝ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    thickenedIndicatorAux δ E₁ ≤ thickenedIndicatorAux δ E₂ :=
  fun _ => tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ENNReal.div_le_div (infEDist_anti subset) rfl.le)

lemma thickenedIndicatorAux_mono_infEDist (δ : ℝ) {E : Set α} {x y : α}
    (h : infEDist x E ≤ infEDist y E) :
    thickenedIndicatorAux δ E y ≤ thickenedIndicatorAux δ E x := by
  simp only [thickenedIndicatorAux]
  rcases le_total (infEDist x E / ENNReal.ofReal δ) 1 with hle | hle
  · rw [ENNReal.sub_le_sub_iff_left hle (by simp)]
    gcongr
  · rw [tsub_eq_zero_of_le hle, tsub_eq_zero_of_le]
    exact hle.trans (by gcongr)

@[deprecated (since := "2026-01-08")]
alias thickenedIndicatorAux_mono_infEdist := thickenedIndicatorAux_mono_infEDist

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
  intro x
  by_cases x_mem_closure : x ∈ closure E
  · simp_rw [thickenedIndicatorAux_one_of_mem_closure _ E x_mem_closure]
    rw [show (indicator (closure E) fun _ => (1 : ℝ≥0∞)) x = 1 by
        simp only [x_mem_closure, indicator_of_mem]]
    exact tendsto_const_nhds
  · rw [show (closure E).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 by
        simp only [x_mem_closure, indicator_of_notMem, not_false_iff]]
    rcases exists_real_pos_lt_infEDist_of_notMem_closure x_mem_closure with ⟨ε, ⟨ε_pos, ε_lt⟩⟩
    rw [Metric.tendsto_nhds] at δseq_lim
    specialize δseq_lim ε ε_pos
    simp only [dist_zero_right, Real.norm_eq_abs, eventually_atTop] at δseq_lim
    rcases δseq_lim with ⟨N, hN⟩
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n n_large
    have key : x ∉ thickening ε E := by simpa only [thickening, mem_setOf_eq, not_lt] using ε_lt.le
    refine le_antisymm ?_ bot_le
    apply (thickenedIndicatorAux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans
    exact (thickenedIndicatorAux_zero ε_pos E key).le

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `infEDist _ E`.

`thickenedIndicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickenedIndicatorAux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps]
def thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : α →ᵇ ℝ≥0 where
  toFun := fun x : α => (thickenedIndicatorAux δ E x).toNNReal
  continuous_toFun := by
    apply ContinuousOn.comp_continuous continuousOn_toNNReal
      (continuous_thickenedIndicatorAux δ_pos E)
    intro x
    exact (lt_of_le_of_lt (@thickenedIndicatorAux_le_one _ _ δ E x) one_lt_top).ne
  map_bounded' := by
    use 2
    intro x y
    rw [NNReal.dist_eq]
    apply (abs_sub _ _).trans
    rw [NNReal.abs_eq, NNReal.abs_eq, ← one_add_one_eq_two]
    have key := @thickenedIndicatorAux_le_one _ _ δ E
    apply add_le_add <;>
      · norm_cast
        exact (toNNReal_le_toNNReal (lt_of_le_of_lt (key _) one_lt_top).ne one_ne_top).mpr (key _)

theorem thickenedIndicator.coeFn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    ⇑(thickenedIndicator δ_pos E) = ENNReal.toNNReal ∘ thickenedIndicatorAux δ E :=
  rfl

theorem thickenedIndicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) (x : α) :
    thickenedIndicator δ_pos E x ≤ 1 := by
  rw [thickenedIndicator.coeFn_eq_comp]
  simpa using (toNNReal_le_toNNReal (by finiteness) one_ne_top).mpr
    (thickenedIndicatorAux_le_one δ E x)

theorem thickenedIndicator_one_of_mem_closure {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_mem : x ∈ closure E) : thickenedIndicator δ_pos E x = 1 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_one_of_mem_closure δ E x_mem, toNNReal_one]

lemma one_le_thickenedIndicator_apply' {X : Type _} [PseudoEMetricSpace X]
    {δ : ℝ} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x ∈ closure F) :
    1 ≤ thickenedIndicator δ_pos F x := by
  rw [thickenedIndicator_one_of_mem_closure δ_pos F hxF]

lemma one_le_thickenedIndicator_apply (X : Type _) [PseudoEMetricSpace X]
    {δ : ℝ} (δ_pos : 0 < δ) {F : Set X} {x : X} (hxF : x ∈ F) :
    1 ≤ thickenedIndicator δ_pos F x :=
  one_le_thickenedIndicator_apply' δ_pos (subset_closure hxF)

theorem thickenedIndicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α} (x_in_E : x ∈ E) :
    thickenedIndicator δ_pos E x = 1 :=
  thickenedIndicator_one_of_mem_closure _ _ (subset_closure x_in_E)

theorem thickenedIndicator_zero {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) {x : α}
    (x_out : x ∉ thickening δ E) : thickenedIndicator δ_pos E x = 0 := by
  rw [thickenedIndicator_apply, thickenedIndicatorAux_zero δ_pos E x_out, toNNReal_zero]

theorem indicator_le_thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    (E.indicator fun _ => (1 : ℝ≥0)) ≤ thickenedIndicator δ_pos E := by
  intro a
  by_cases h : a ∈ E
  · simp only [h, indicator_of_mem, thickenedIndicator_one δ_pos E h, le_refl]
  · simp only [h, indicator_of_notMem, not_false_iff, zero_le]

theorem thickenedIndicator_mono {δ₁ δ₂ : ℝ} (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂)
    (E : Set α) : ⇑(thickenedIndicator δ₁_pos E) ≤ thickenedIndicator δ₂_pos E := by
  intro x
  apply (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
  apply thickenedIndicatorAux_mono hle

theorem thickenedIndicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : Set α} (subset : E₁ ⊆ E₂) :
    ⇑(thickenedIndicator δ_pos E₁) ≤ thickenedIndicator δ_pos E₂ := fun x =>
  (toNNReal_le_toNNReal (by finiteness) (by finiteness)).mpr
    (thickenedIndicatorAux_subset δ subset x)

@[gcongr]
lemma thickenedIndicator_mono_infEDist {δ : ℝ} (δ_pos : 0 < δ) {E : Set α} {x y : α}
    (h : infEDist x E ≤ infEDist y E) :
    thickenedIndicator δ_pos E y ≤ thickenedIndicator δ_pos E x := by
  simp only [thickenedIndicator_apply]
  gcongr
  · finiteness
  · exact thickenedIndicatorAux_mono_infEDist δ h

@[deprecated (since := "2026-01-08")]
alias thickenedIndicator_mono_infEdist := thickenedIndicator_mono_infEDist

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
  rw [tendsto_pi_nhds] at *
  intro x
  rw [show indicator (closure E) (fun _ => (1 : ℝ≥0)) x =
        (indicator (closure E) (fun _ => (1 : ℝ≥0∞)) x).toNNReal
      by refine (congr_fun (comp_indicator_const 1 ENNReal.toNNReal toNNReal_zero) x).symm]
  refine Tendsto.comp (tendsto_toNNReal ?_) (key x)
  by_cases x_mem : x ∈ closure E <;> simp [x_mem]

lemma lipschitzWith_thickenedIndicator {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    LipschitzWith δ.toNNReal⁻¹ (thickenedIndicator δ_pos E) := by
  intro x y
  wlog h : infEDist x E ≤ infEDist y E generalizing x y
  · specialize this y x (le_of_not_ge h)
    rwa [edist_comm, edist_comm x]
  simp_rw [edist_dist, NNReal.dist_eq, thickenedIndicator_apply, coe_toNNReal_eq_toReal]
  rw [← ENNReal.toReal_sub_of_le (thickenedIndicatorAux_mono_infEDist _ h) (by finiteness)]
  simp only [thickenedIndicatorAux, abs_toReal, ne_eq, sub_eq_top_iff, one_ne_top, false_and,
    not_false_eq_true, and_true, ofReal_toReal]
  rw [ENNReal.coe_inv (by simp [δ_pos]), ENNReal.ofReal, div_eq_mul_inv, div_eq_mul_inv]
  by_cases h_le : infEDist y E * (↑δ.toNNReal)⁻¹ ≤ 1
  · calc 1 - infEDist x E * (↑δ.toNNReal)⁻¹ - (1 - infEDist y E * (↑δ.toNNReal)⁻¹)
    _ ≤ infEDist y E * (↑δ.toNNReal)⁻¹ - infEDist x E * (↑δ.toNNReal)⁻¹ := by
      rw [ENNReal.sub_sub_sub_cancel_left (by finiteness) h_le]
    _ ≤ (↑δ.toNNReal)⁻¹ * edist x y := by
      rw [← ENNReal.sub_mul (by simp [δ_pos]), mul_comm, edist_comm]
      gcongr
      simp only [tsub_le_iff_right]
      exact infEDist_le_edist_add_infEDist
  · simp only [tsub_le_iff_right]
    rw [tsub_eq_zero_of_le (not_le.mp h_le).le, add_zero, mul_comm]
    calc 1
    _ ≤ infEDist y E * (↑δ.toNNReal)⁻¹ := (not_le.mp h_le).le
    _ ≤ edist x y * (↑δ.toNNReal)⁻¹ + infEDist x E * (↑δ.toNNReal)⁻¹ := by
      rw [← add_mul, edist_comm]
      gcongr
      exact infEDist_le_edist_add_infEDist

end thickenedIndicator

section indicator

variable {α : Type*} [PseudoEMetricSpace α] {β : Type*} [One β]

/-- Pointwise, the multiplicative indicators of δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ>0 tends to zero. -/
@[to_additive /-- Pointwise, the indicators of δ-thickenings of a set eventually coincide
with the indicator of the set as δ>0 tends to zero. -/]
lemma mulIndicator_thickening_eventually_eq_mulIndicator_closure (f : α → β) (E : Set α) (x : α) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (Metric.thickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x ∈ closure E
  · filter_upwards [self_mem_nhdsWithin] with δ δ_pos
    simp only [closure_subset_thickening δ_pos E x_mem_closure, mulIndicator_of_mem, x_mem_closure]
  · have obs := eventually_notMem_thickening_of_infEDist_pos x_mem_closure
    filter_upwards [mem_nhdsWithin_of_mem_nhds obs, self_mem_nhdsWithin]
      with δ x_notin_thE _
    simp only [x_notin_thE, not_false_eq_true, mulIndicator_of_notMem, x_mem_closure]

/-- Pointwise, the multiplicative indicators of closed δ-thickenings of a set eventually coincide
with the multiplicative indicator of the set as δ tends to zero. -/
@[to_additive /-- Pointwise, the indicators of closed δ-thickenings of a set eventually coincide
with the indicator of the set as δ tends to zero. -/]
lemma mulIndicator_cthickening_eventually_eq_mulIndicator_closure (f : α → β) (E : Set α) (x : α) :
    ∀ᶠ δ in 𝓝 (0 : ℝ),
      (Metric.cthickening δ E).mulIndicator f x = (closure E).mulIndicator f x := by
  by_cases x_mem_closure : x ∈ closure E
  · filter_upwards [univ_mem] with δ _
    have obs : x ∈ cthickening δ E := closure_subset_cthickening δ E x_mem_closure
    rw [mulIndicator_of_mem obs f, mulIndicator_of_mem x_mem_closure f]
  · filter_upwards [eventually_notMem_cthickening_of_infEDist_pos x_mem_closure] with δ hδ
    simp only [hδ, not_false_eq_true, mulIndicator_of_notMem, x_mem_closure]

variable [TopologicalSpace β]

/-- The multiplicative indicators of δ-thickenings of a set tend pointwise to the multiplicative
indicator of the set, as δ>0 tends to zero. -/
@[to_additive /-- The indicators of δ-thickenings of a set tend pointwise to the indicator of the
set, as δ>0 tends to zero. -/]
lemma tendsto_mulIndicator_thickening_mulIndicator_closure (f : α → β) (E : Set α) :
    Tendsto (fun δ ↦ (Metric.thickening δ E).mulIndicator f) (𝓝[>] 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_thickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

/-- The multiplicative indicators of closed δ-thickenings of a set tend pointwise to the
multiplicative indicator of the set, as δ tends to zero. -/
@[to_additive /-- The indicators of closed δ-thickenings of a set tend pointwise to the indicator
of the set, as δ tends to zero. -/]
lemma tendsto_mulIndicator_cthickening_mulIndicator_closure (f : α → β) (E : Set α) :
    Tendsto (fun δ ↦ (Metric.cthickening δ E).mulIndicator f) (𝓝 0)
      (𝓝 ((closure E).mulIndicator f)) := by
  rw [tendsto_pi_nhds]
  intro x
  rw [tendsto_congr' (mulIndicator_cthickening_eventually_eq_mulIndicator_closure f E x)]
  apply tendsto_const_nhds

end indicator
