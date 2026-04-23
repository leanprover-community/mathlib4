/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure

/-!
# Applications of the Hausdorff distance in normed spaces

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace `F` of `E`, there is a nonzero `x` such that `‖x - F‖`
is at least `r * ‖x‖` for any `r < 1`. This is `riesz_lemma`.

In a nontrivially normed field (with an element `c` of norm `> 1`) and any `R > ‖c‖`, one can
guarantee `‖x‖ ≤ R` and `‖x - y‖ ≥ 1` for any `y` in `F`. This is `riesz_lemma_of_norm_lt`.

For a normed space over an `RCLike` field, one can find an element of norm exactly `1` with the same
property. This is `riesz_lemma_one`.

A further lemma, `Metric.closedBall_infDist_compl_subset_closure`, finds a *closed* ball within
the closure of a set `s` of optimal distance from a point in `x` to the frontier of `s`.
-/

public section


open Set Metric

open Topology

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]

/-- Riesz's lemma, which usually states that it is possible to find a
vector with norm 1 whose distance to a closed proper subspace is
arbitrarily close to 1. The statement here is in terms of multiples of
norms, since in general the existence of an element of norm exactly 1
is not guaranteed. For a variant giving an element with norm in `[1, R]`, see
`riesz_lemma_of_norm_lt`, and for a variant giving an element with norm
exactly one assuming stronger assumptions on the underlying field, see
`riesz_lemma_of_lt_one`. -/
theorem riesz_lemma {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) {r : ℝ}
    (hr : r < 1) : ∃ x₀ : E, x₀ ∉ F ∧ ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖ := by
  classical
    obtain ⟨x, hx⟩ : ∃ x : E, x ∉ F := hF
    let d := Metric.infDist x F
    have hFn : (F : Set E).Nonempty := ⟨_, F.zero_mem⟩
    have hdp : 0 < d :=
      lt_of_le_of_ne Metric.infDist_nonneg fun heq =>
        hx ((hFc.mem_iff_infDist_zero hFn).2 heq.symm)
    let r' := max r 2⁻¹
    have hr' : r' < 1 := by
      simp only [r', max_lt_iff, hr, true_and]
      norm_num
    have hlt : 0 < r' := lt_of_lt_of_le (by simp) (le_max_right r 2⁻¹)
    have hdlt : d < d / r' := (lt_div_iff₀ hlt).mpr ((mul_lt_iff_lt_one_right hdp).2 hr')
    obtain ⟨y₀, hy₀F, hxy₀⟩ : ∃ y ∈ F, dist x y < d / r' := (Metric.infDist_lt_iff hFn).mp hdlt
    have x_ne_y₀ : x - y₀ ∉ F := by
      by_contra h
      have : x - y₀ + y₀ ∈ F := F.add_mem h hy₀F
      simp only [neg_add_cancel_right, sub_eq_add_neg] at this
      exact hx this
    refine ⟨x - y₀, x_ne_y₀, fun y hy => le_of_lt ?_⟩
    have hy₀y : y₀ + y ∈ F := F.add_mem hy₀F hy
    calc
      r * ‖x - y₀‖ ≤ r' * ‖x - y₀‖ := by gcongr; apply le_max_left
      _ < d := by
        rw [← dist_eq_norm]
        exact (lt_div_iff₀' hlt).1 hxy₀
      _ ≤ dist x (y₀ + y) := Metric.infDist_le_dist_of_mem hy₀y
      _ = ‖x - y₀ - y‖ := by rw [sub_sub, dist_eq_norm]

/--
A version of Riesz lemma: given a strict closed subspace `F`, one may find an element of norm `≤ R`
which is at distance at least `1` of every element of `F`. Here, `R` is any given constant
strictly larger than the norm of an element of norm `> 1`. For a version without an `R`, see
`riesz_lemma`, and for a variant giving an element with norm
exactly one assuming stronger assumptions on the underlying field, see
`riesz_lemma_of_lt_one`.

Since we are considering a general nontrivially normed field, there may be a gap in possible norms
(for instance no element of norm in `(1,2)`). Hence, we cannot allow `R` arbitrarily close to `1`,
and require `R > ‖c‖` for some `c : 𝕜` with norm `> 1`.
-/
theorem riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) :
    ∃ x₀ : E, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR
  have : ‖c‖ / R < 1 := by
    rw [div_lt_iff₀ Rpos]
    simpa using hR
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
  have x0 : x ≠ 0 := fun H => by simp [H] at xF
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < R ∧ R / ‖c‖ ≤ ‖d • x‖ ∧ ‖d‖⁻¹ ≤ R⁻¹ * ‖c‖ * ‖x‖ :=
    rescale_to_shell hc Rpos x0
  refine ⟨d • x, dxlt.le, fun y hy => ?_⟩
  set y' := d⁻¹ • y
  have yy' : y = d • y' := by simp [y', smul_smul, mul_inv_cancel₀ d0]
  calc
    1 = ‖c‖ / R * (R / ‖c‖) := by field
    _ ≤ ‖c‖ / R * ‖d • x‖ := by gcongr
    _ = ‖d‖ * (‖c‖ / R * ‖x‖) := by
      simp only [norm_smul]
      ring
    _ ≤ ‖d‖ * ‖x - y'‖ := by gcongr; exact hx y' (by simp [y', Submodule.smul_mem _ _ hy])
    _ = ‖d • x - y‖ := by rw [yy', ← smul_sub, norm_smul]

theorem Metric.closedBall_infDist_compl_subset_closure {x : F} {s : Set F} (hx : x ∈ s) :
    closedBall x (infDist x sᶜ) ⊆ closure s := by
  rcases eq_or_ne (infDist x sᶜ) 0 with h₀ | h₀
  · rw [h₀, closedBall_zero']
    exact closure_mono (singleton_subset_iff.2 hx)
  · rw [← closure_ball x h₀]
    exact closure_mono ball_infDist_compl_subset

/--
A version of Riesz lemma: given a proper closed subspace `F`, one may find an element of norm `1`
which is at distance at least `r` of every element of `F`, for any `r < 1`.
For a version with weaker assumptions on the underlying field, see `riesz_lemma` or
`riesz_lemma_of_norm_lt`.
-/
theorem riesz_lemma_of_lt_one {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Subspace 𝕜 E} (hFc : IsClosed (F : Set E)) (hF : ∃ (x : E), x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ ∉ F, ‖x₀‖ = 1 ∧ ∀ y ∈ F, r ≤ ‖x₀ - y‖ := by
  obtain ⟨x₀, hx₀, h⟩ := riesz_lemma hFc hF hr
  have hx₀' : x₀ ≠ 0 := by rintro rfl; simp at hx₀
  refine ⟨(‖x₀‖⁻¹ : 𝕜) • x₀, ?_, norm_smul_inv_norm hx₀', ?_⟩
  · rwa [Submodule.smul_mem_iff]
    simpa
  intro y hy
  have h₂ : ‖(‖x₀‖ : 𝕜)⁻¹ • (x₀ - (‖x₀‖ : 𝕜) • y)‖ = ‖x₀‖⁻¹ * ‖x₀ - (‖x₀‖ : 𝕜) • y‖ := by
    rw [norm_smul, norm_inv, norm_algebraMap', norm_norm]
  have h₁ := h ((‖x₀‖ : 𝕜) • y) (F.smul_mem _ hy)
  rwa [← le_inv_mul_iff₀' (by simpa), ← h₂, smul_sub, inv_smul_smul₀] at h₁
  simpa using hx₀'
