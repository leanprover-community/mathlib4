/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Infinite products in normed rings

This file proves a dominated convergence theorem for infinite products of terms of the form
`(1 + f n k)` in a complete normed commutative ring, by reducing to the additive version
(Tannery's theorem) via the formal expansion `∏ (1 + f i) = ∑ₛ ∏ᵢ∈ₛ f i`.

## Main results

* `tendsto_tprod_one_add_of_dominated_convergence`: if `f n k → g k` pointwise and
  `‖f n k‖ ≤ bound k` eventually with `bound` summable, then
  `∏' k, (1 + f n k) → ∏' k, (1 + g k)`.
-/

open Topology Filter

variable {α R β : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {g : β → R}
  {bound : β → ℝ}

/-- Dominated convergence for infinite products: if `f n k → g k` for all `k` and
`‖f n k‖ ≤ bound k` eventually with `bound` summable,
then `∏' k, (1 + f n k) → ∏' k, (1 + g k)`. -/
public theorem tendsto_tprod_one_add_of_dominated_convergence {𝓕 : Filter α} {f : α → β → R}
    (h_sum : Summable bound) (hab : ∀ k, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∏' k, (1 + f n k)) 𝓕 (𝓝 (∏' k, (1 + g k))) := by
  rcases eq_or_neBot 𝓕 with rfl | _
  · simp
  have h_bound_g (k) : ‖g k‖ ≤ bound k :=
    le_of_tendsto ((hab k).norm) (h_bound.mono fun n hn ↦ hn k)
  have hsum_g : Summable (‖g ·‖) := h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound_g
  rw [show ∏' k, (1 + g k) = ∑' s, ∏ i ∈ s, g i from
    tprod_one_add (summable_finset_prod_of_summable_norm hsum_g)]
  have : Tendsto (∑' k, ∏ c ∈ k, f · c) 𝓕 (𝓝 (∑' k, ∏ c ∈ k, g c)) :=
    tendsto_tsum_of_dominated_convergence (summable_finset_prod_of_summable_nonneg
      (fun i ↦ (norm_nonneg (g i)).trans (h_bound_g i)) h_sum)
      (tendsto_finset_prod · fun i _ ↦ hab i)
      (h_bound.mono fun n hn s ↦ (Finset.norm_prod_le s (f n)).trans
      (Finset.prod_le_prod (by grind) (by grind)))
  apply this.congr' (h_bound.mono fun n hn ↦ ?_)
  rw [tprod_one_add]
  exact summable_finset_prod_of_summable_norm <| h_sum.of_nonneg_of_le (by grind) hn
