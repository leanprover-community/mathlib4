/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Gauge
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Closure
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
/-!
# "Gauge rescale" homeomorphism between convex sets

Given two convex von Neumann bounded neighbourhoods of the origin
in a real topological vector space,
we construct a homeomorphism `gaugeRescaleHomeomorph`
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.
-/

@[expose] public section

open Metric Bornology Filter Set
open scoped NNReal Topology Pointwise

noncomputable section

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The gauge rescale map `gaugeRescale s t` sends each point `x` to the point `y` on the same ray
that has the same gauge w.r.t. `t` as `x` has w.r.t. `s`.

The characteristic property is satisfied if `gauge t x ≠ 0`, see `gauge_gaugeRescale'`.
In particular, it is satisfied for all `x`,
provided that `t` is absorbent and von Neumann bounded. -/
def gaugeRescale (s t : Set E) (x : E) : E := (gauge s x / gauge t x) • x

theorem gaugeRescale_def (s t : Set E) (x : E) :
    gaugeRescale s t x = (gauge s x / gauge t x) • x :=
  rfl

@[simp] theorem gaugeRescale_zero (s t : Set E) : gaugeRescale s t 0 = 0 := smul_zero _

theorem gaugeRescale_smul (s t : Set E) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    gaugeRescale s t (c • x) = c • gaugeRescale s t x := by
  simp only [gaugeRescale, gauge_smul_of_nonneg hc, smul_smul, smul_eq_mul]
  rw [mul_div_mul_comm, mul_right_comm, div_self_mul_self]

theorem gauge_gaugeRescale' (s : Set E) {t : Set E} {x : E} (hx : gauge t x ≠ 0) :
    gauge t (gaugeRescale s t x) = gauge s x := by
  rw [gaugeRescale, gauge_smul_of_nonneg (div_nonneg (gauge_nonneg _) (gauge_nonneg _)),
    smul_eq_mul, div_mul_cancel₀ _ hx]

theorem gauge_gaugeRescale_le (s t : Set E) (x : E) :
    gauge t (gaugeRescale s t x) ≤ gauge s x := by
  by_cases hx : gauge t x = 0
  · simp [gaugeRescale, hx, gauge_nonneg]
  · exact (gauge_gaugeRescale' s hx).le

variable [TopologicalSpace E]

section
variable [T1Space E]

theorem gaugeRescale_self_apply {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (x : E) : gaugeRescale s s x = x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale, div_self, one_smul]
  exact ((gauge_pos hsa hsb).2 hx).ne'

theorem gaugeRescale_self {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s) :
    gaugeRescale s s = id :=
  funext <| gaugeRescale_self_apply hsa hsb

theorem gauge_gaugeRescale (s : Set E) {t : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gauge t (gaugeRescale s t x) = gauge s x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact gauge_gaugeRescale' s ((gauge_pos hta htb).2 hx).ne'

theorem gaugeRescale_gaugeRescale {s t u : Set E} (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t)
    (x : E) : gaugeRescale t u (gaugeRescale s t x) = gaugeRescale s u x := by
  rcases eq_or_ne x 0 with rfl | hx; · simp
  rw [gaugeRescale_def s t x, gaugeRescale_smul, gaugeRescale, gaugeRescale, smul_smul,
    div_mul_div_cancel₀]
  exacts [((gauge_pos hta htb).2 hx).ne', div_nonneg (gauge_nonneg _) (gauge_nonneg _)]

/-- `gaugeRescale` bundled as an `Equiv`. -/
def gaugeRescaleEquiv (s t : Set E) (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t) : E ≃ E where
  toFun := gaugeRescale s t
  invFun := gaugeRescale t s
  left_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption
  right_inv x := by rw [gaugeRescale_gaugeRescale, gaugeRescale_self_apply] <;> assumption

end

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s t : Set E}

theorem mapsTo_gaugeRescale_interior (h₀ : t ∈ 𝓝 0) (hc : Convex ℝ t) :
    MapsTo (gaugeRescale s t) (interior s) (interior t) := fun x hx ↦ by
  rw [← gauge_lt_one_iff_mem_interior] <;> try assumption
  exact (gauge_gaugeRescale_le _ _ _).trans_lt (interior_subset_gauge_lt_one _ hx)

theorem mapsTo_gaugeRescale_closure {s t : Set E} (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (htc : Convex ℝ t) (ht₀ : 0 ∈ t) (hta : Absorbent ℝ t) :
    MapsTo (gaugeRescale s t) (closure s) (closure t) := fun _x hx ↦
  mem_closure_of_gauge_le_one htc ht₀ hta <| (gauge_gaugeRescale_le _ _ _).trans <|
    (gauge_le_one_iff_mem_closure hsc hs₀).2 hx

variable [T1Space E]

theorem continuous_gaugeRescale {s t : Set E} (hs : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (ht : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    Continuous (gaugeRescale s t) := by
  have hta : Absorbent ℝ t := absorbent_nhds_zero ht₀
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    simp only [tendsto_comap_iff, Function.comp_def, gauge_gaugeRescale _ hta htb]
    exact tendsto_gauge_nhds_zero hs₀
  · exact ((continuousAt_gauge hs hs₀).div (continuousAt_gauge ht ht₀)
      ((gauge_pos hta htb).2 hx).ne').smul continuousAt_id

/-- `gaugeRescale` bundled as a `Homeomorph`. -/
def gaugeRescaleHomeomorph (s t : Set E)
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) : E ≃ₜ E where
  toEquiv := gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := by apply continuous_gaugeRescale <;> assumption
  continuous_invFun := by apply continuous_gaugeRescale <;> assumption

theorem image_gaugeRescaleHomeomorph_interior {s t : Set E}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' interior s = interior t :=
  Subset.antisymm (mapsTo_gaugeRescale_interior ht₀ htc).image_subset <| by
    rw [← Homeomorph.preimage_symm, ← image_subset_iff]
    exact (mapsTo_gaugeRescale_interior hs₀ hsc).image_subset

theorem image_gaugeRescaleHomeomorph_closure {s t : Set E}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' closure s = closure t := by
  refine Subset.antisymm (mapsTo_gaugeRescale_closure hsc hs₀ htc
    (mem_of_mem_nhds ht₀) (absorbent_nhds_zero ht₀)).image_subset ?_
  rw [← Homeomorph.preimage_symm, ← image_subset_iff]
  exact (mapsTo_gaugeRescale_closure htc ht₀ hsc
    (mem_of_mem_nhds hs₀) (absorbent_nhds_zero hs₀)).image_subset

/-- Given two convex bounded sets in a topological vector space with nonempty interiors,
there exists a homeomorphism of the ambient space
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.

In particular, if both `s` and `t` are open set or both `s` and `t` are closed sets,
then `e` maps `s` to `t`. -/
theorem exists_homeomorph_image_eq {s t : Set E}
    (hsc : Convex ℝ s) (hsne : (interior s).Nonempty) (hsb : IsVonNBounded ℝ s)
    (hst : Convex ℝ t) (htne : (interior t).Nonempty) (htb : IsVonNBounded ℝ t) :
    ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t ∧
      e '' frontier s = frontier t := by
  rsuffices ⟨e, h₁, h₂⟩ : ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t
  · refine ⟨e, h₁, h₂, ?_⟩
    simp_rw [← closure_diff_interior, image_diff e.injective, h₁, h₂]
  rcases hsne with ⟨x, hx⟩
  rcases htne with ⟨y, hy⟩
  set h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
  refine ⟨.trans (.addLeft (-x)) <| h.trans <| .addLeft y, ?_, ?_⟩
  · calc
      (fun a ↦ y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
        simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
  · calc
      (fun a ↦ y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
        simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `s` is a convex bounded set with a nonempty interior in a real normed space,
then there is a homeomorphism of the ambient space to itself
that sends the interior of `s` to the unit open ball
and the closure of `s` to the unit closed ball. -/
theorem exists_homeomorph_image_interior_closure_frontier_eq_unitBall {s : Set E}
    (hc : Convex ℝ s) (hne : (interior s).Nonempty) (hb : IsBounded s) :
    ∃ h : E ≃ₜ E, h '' interior s = ball 0 1 ∧ h '' closure s = closedBall 0 1 ∧
      h '' frontier s = sphere 0 1 := by
  simpa [isOpen_ball.interior_eq, closure_ball, frontier_ball]
    using exists_homeomorph_image_eq hc hne (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (by simp [isOpen_ball.interior_eq]) (NormedSpace.isVonNBounded_ball _ _ _)
