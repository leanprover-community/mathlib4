/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.Real
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.MetricSpace.HausdorffDistance

#align_import analysis.normed_space.riesz_lemma from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Applications of the Hausdorff distance in normed spaces

Riesz's lemma, stated for a normed space over a normed field: for any
closed proper subspace `F` of `E`, there is a nonzero `x` such that `‖x - F‖`
is at least `r * ‖x‖` for any `r < 1`. This is `riesz_lemma`.

In a nontrivially normed field (with an element `c` of norm `> 1`) and any `R > ‖c‖`, one can
guarantee `‖x‖ ≤ R` and `‖x - y‖ ≥ 1` for any `y` in `F`. This is `riesz_lemma_of_norm_lt`.

A further lemma, `Metric.closedBall_infDist_compl_subset_closure`, finds a *closed* ball within
the closure of a set `s` of optimal distance from a point in `x` to the frontier of `s`.
-/


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
`riesz_lemma_of_norm_lt`. -/
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
      simp only [r', ge_iff_le, max_lt_iff, hr, true_and]
      norm_num
    have hlt : 0 < r' := lt_of_lt_of_le (by norm_num) (le_max_right r 2⁻¹)
    have hdlt : d < d / r' := (lt_div_iff hlt).mpr ((mul_lt_iff_lt_one_right hdp).2 hr')
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
        exact (lt_div_iff' hlt).1 hxy₀
      _ ≤ dist x (y₀ + y) := Metric.infDist_le_dist_of_mem hy₀y
      _ = ‖x - y₀ - y‖ := by rw [sub_sub, dist_eq_norm]
#align riesz_lemma riesz_lemma

/--
A version of Riesz lemma: given a strict closed subspace `F`, one may find an element of norm `≤ R`
which is at distance at least `1` of every element of `F`. Here, `R` is any given constant
strictly larger than the norm of an element of norm `> 1`. For a version without an `R`, see
`riesz_lemma`.

Since we are considering a general nontrivially normed field, there may be a gap in possible norms
(for instance no element of norm in `(1,2)`). Hence, we can not allow `R` arbitrarily close to `1`,
and require `R > ‖c‖` for some `c : 𝕜` with norm `> 1`.
-/
theorem riesz_lemma_of_norm_lt {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R) {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) :
    ∃ x₀ : E, ‖x₀‖ ≤ R ∧ ∀ y ∈ F, 1 ≤ ‖x₀ - y‖ := by
  have Rpos : 0 < R := (norm_nonneg _).trans_lt hR
  have : ‖c‖ / R < 1 := by
    rw [div_lt_iff Rpos]
    simpa using hR
  rcases riesz_lemma hFc hF this with ⟨x, xF, hx⟩
  have x0 : x ≠ 0 := fun H => by simp [H] at xF
  obtain ⟨d, d0, dxlt, ledx, -⟩ :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < R ∧ R / ‖c‖ ≤ ‖d • x‖ ∧ ‖d‖⁻¹ ≤ R⁻¹ * ‖c‖ * ‖x‖ :=
    rescale_to_shell hc Rpos x0
  refine ⟨d • x, dxlt.le, fun y hy => ?_⟩
  set y' := d⁻¹ • y
  have yy' : y = d • y' := by simp [y', smul_smul, mul_inv_cancel d0]
  calc
    1 = ‖c‖ / R * (R / ‖c‖) := by field_simp [Rpos.ne', (zero_lt_one.trans hc).ne']
    _ ≤ ‖c‖ / R * ‖d • x‖ := by gcongr
    _ = ‖d‖ * (‖c‖ / R * ‖x‖) := by
      simp only [norm_smul]
      ring
    _ ≤ ‖d‖ * ‖x - y'‖ := by gcongr; exact hx y' (by simp [Submodule.smul_mem _ _ hy])
    _ = ‖d • x - y‖ := by rw [yy', ← smul_sub, norm_smul]
#align riesz_lemma_of_norm_lt riesz_lemma_of_norm_lt

theorem Metric.closedBall_infDist_compl_subset_closure {x : F} {s : Set F} (hx : x ∈ s) :
    closedBall x (infDist x sᶜ) ⊆ closure s := by
  rcases eq_or_ne (infDist x sᶜ) 0 with h₀ | h₀
  · rw [h₀, closedBall_zero']
    exact closure_mono (singleton_subset_iff.2 hx)
  · rw [← closure_ball x h₀]
    exact closure_mono ball_infDist_compl_subset
#align metric.closed_ball_inf_dist_compl_subset_closure Metric.closedBall_infDist_compl_subset_closure
