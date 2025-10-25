/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.AbsMax

/-!
# Borel-Caratheodory theorem

This file proves the Borel-Caratheodory theorem, in the version that is needed for
the PrimeNumberTheoremAnd/StrongPNT [kontorovich2025] project of Alex Kontorovich and
Terence Tao. This version is also used in most textbook proofs of the Prime Number Theorem.

## Main results.

`borelCaratheodory_closedBall`

Let $R, M>0$. Let $f$ be analytic on $|z|≤ R$ such that $f(0) = 0$ and suppose
$\mathfrak{R}f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
$$
  \sup_{|z|\leq r}|f(z)|\leq\frac{2Mr}{R-r}.
$$

We also provide a variant that does not require vanishing of $f$ at $0$.
This version aligns with the statement of the Theorem available on Wikipedia.

`borelCaratheodory_closedBall'`

Let $R, M>0$. Let $f$ be analytic on $|z|≤ R$ and suppose $\mathfrak{R}f(z)\leq M$
for all $|z|\leq R$. Then for any $0 < r < R$,
$$
  \sup_{|z|\leq r}|f(z)|\leq\frac{2Mr}{R-r} + |f(0)|\frac{R+r}{R-r}.
$$

## Implementation notes

The proof relies on the fact that if $f(0) = 0$ and $f$ is analytic in $|z| ≤ R$
with $R > 0$ then $f(z) / z$ is also analytic in $|z| ≤ R$. To avoid repetition
the file defines in `divRemovableZero` a function equal to $f(z) / z$ for
$z ≠ 0$ and equal to $f'(0)$ for $z = 0$. No restriction to $f$ with
$f(0) = 0$ is made in this definition.

In `AnalyticOn.divRemovableZero` we prove that if $f$ is analytic in an open
set containing zero, and $f(0) = 0$ then $f(z) / z$ is analytic in the same
open set.

In `AnalyticOn.divRemovableZero_closedBall` we prove the same statement for
functions analytic on closed balls $|z| ≤ R$. As is the proof is a little bit
awkward, it would be more natural to prove that if $f$ is analytic in $|z| ≤ R$,
then it is analytic on an open set containing $|z| ≤ R$ and appeal to the
previous result.

In `schwartzQuotient` we define the Schwartz quotient
$$
  \frac{f(z) / z}{2 * M - f(z)}
$$
on which the proof of Borel-Caratheodory hinges. No restrictions that
$f(0) = 0$ or $2 M - f(z) ≠ 0$ are placed in this definition.

In `AnalyticOn.schwartzQuotient` we prove that the Schwarz quotient is analytic
in $|z| ≤ R$ provided that $f$ is analytic in $|z| ≤ R$ and $f(0) = 0$ and
$2 * M - f(z) ≠ 0$ for all $|z| ≤ R$. The latter condition will be implied by
the assumption $\Re{f(z)} ≤ M$ in Borel-Caratheodory.

In `Complex.norm_le_norm_two_mul_sub_of_re_le` we prove an elementary inequality
asserting that if $\Re{x} ≤ M$ then $|x| ≤ |2 M - x|$. This is used in the
proof of Borel-Caratheodory.

The function `AnalyticOn.norm_le_of_norm_le_on_sphere` is a specialization
of the maximum modulus principle to the case of $|z| ≤ R$. Since the proof of
Borel-Caratheodory uses the maximum modulus twice on this domain, it is handy
to have a dedicated function for this domain. The statement allows for a
conclusion specialized to $|z| ≤ r$ with $r ≤ R$. This is of course trivial,
and the only reason to include such a conclusion, is because this form of
the conclusion is used twice in the proof of Borel-Caratheodory.

In `borelCaratheodory_closedBall` we prove the Borel-Caratheodory
theorem under the assumption that $f(0) = 0$. This proof of Borel-Caratheodory
follows the blueprint laid out in the StrongPNT project [kontorovich2025].

Finally in `borelCaratheodory_closedBall'` we deduce from
`borelCaratheodory_closedBall` a version of Borel-Caratheodory that does
not assume vanishing of $f$ at $0$. This version matches the statement of
the theorem as seen in Wikipedia.

## References

* [Alex Kontorovich et al., *PrimeNumberTheoremAnd*][kontorovich2025]
* <https://en.wikipedia.org/wiki/Borel%E2%80%93Carath%C3%A9odory_theorem>

## Tags

Borel-Caratheodory, borel, caratheodory, complex, analytic, prime number theorem

-/

/-- Given `f`, the function `divRemovableZero f` defines a function equal
to `f z / z` for `z ≠ 0` and equal to `deriv f 0` for `z = 0`. -/
noncomputable abbrev divRemovableZero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z) / z) 0 ((deriv f) 0)

/-- For `z ≠ 0`, `divRemovableZero f z` is equal to `f z / z`. -/
lemma divRemovableZero_of_ne_zero {z : ℂ} (f : ℂ → ℂ)
    (z_ne_0 : z ≠ 0) : divRemovableZero f z = f z / z := by
  unfold divRemovableZero; apply Function.update_of_ne z_ne_0

/-- If `f` is analytic on an open set `s` and `f 0 = 0` then `f z / z` is also
analytic on `s`. -/
lemma AnalyticOn.divRemovableZero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds (0 : ℂ)) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) : AnalyticOn ℂ (divRemovableZero f) s := by
  rw [Complex.analyticOn_iff_differentiableOn o]
  rw [←(Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0)]
  constructor
  · rw [differentiableOn_congr
          (by
            intro x hyp_x
            apply Function.update_of_ne
            rw [Set.mem_diff, Set.mem_singleton_iff] at hyp_x
            rw [ne_eq]; exact hyp_x.right) ]

    exact DifferentiableOn.fun_div
      (AnalyticOn.differentiableOn (AnalyticOn.mono analytic Set.diff_subset))
      (DifferentiableOn.mono (differentiableOn_id (s := Set.univ))
      (Set.subset_univ (s \ {0})))
      (by
        intro x hyp_x
        rw [Set.mem_diff, Set.mem_singleton_iff] at hyp_x
        rw [ne_eq]; exact hyp_x.right)

  · have U := HasDerivAt.continuousAt_div (c := 0) (a := (deriv f) 0) (f := f)
      (DifferentiableOn.hasDerivAt
         ((Complex.analyticOn_iff_differentiableOn o).mp analytic) sInNhds0)
    have T : (fun (x : ℂ) ↦ (f x - 0) / (x - 0)) = (fun (x : ℂ) ↦ (f x) / x) := by
      funext x; rw [sub_zero, sub_zero]
    rw [zero, T] at U; exact U

/-- If `f` is analytic on `|z| ≤ R` and `f 0 = 0` then `f z / z` is analytic in
`|z| ≤ R`. -/
lemma AnalyticOn.divRemovableZero_closedBall {f : ℂ → ℂ} {R : ℝ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R)) (zero : f 0 = 0) :
    AnalyticOn ℂ (_root_.divRemovableZero f) (Metric.closedBall (0 : ℂ) R) := by
  apply analyticOn_of_locally_analyticOn
  intro x x_hyp
  by_cases h : ‖x‖ = R
  · use Metric.ball x (R / 2)
    constructor
    · exact Metric.isOpen_ball
    · constructor
      · simp only [Metric.mem_ball, dist_self, Nat.ofNat_pos,
                   div_pos_iff_of_pos_right]; positivity
      · have Z : ∀ w ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2),
                   _root_.divRemovableZero f w = f w / w := by
          intro x₂ hyp_x₂
          apply divRemovableZero_of_ne_zero
          rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall,
              dist_zero_right, Set.mem_setOf_eq] at hyp_x₂
          rw [← norm_pos_iff]
          calc 0
            _ < R - ‖x₂ - x‖ := by let ⟨u,v⟩ := hyp_x₂; linarith
            _ = ‖x‖ - ‖x - x₂‖ := by rw [h]; simp only [sub_right_inj]; apply norm_sub_rev
            _ ≤ ‖x - (x - x₂)‖ := by apply norm_sub_norm_le
            _ ≤ ‖x₂‖ := by simp only [sub_sub_cancel, le_refl]

        apply AnalyticOn.congr
        · apply AnalyticOn.div (AnalyticOn.mono analytic Set.inter_subset_left) analyticOn_id
          · intro x₁ hyp_x₁
            rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall,
                dist_zero_right, Set.mem_setOf_eq] at hyp_x₁
            rw [← norm_pos_iff]
            calc 0
              _ < R - ‖x₁ - x‖ := by let ⟨u,v⟩ := hyp_x₁; linarith
              _ = ‖x‖ - ‖-(x₁ - x)‖ := by rw [h, neg_sub, sub_right_inj]; apply norm_sub_rev
              _ ≤ ‖x - (-(x₁ - x))‖ := by apply norm_sub_norm_le
              _ = ‖x₁‖ := by rw [neg_sub, sub_sub_cancel]

        · simp only [Set.EqOn.eq_1, Set.mem_inter_iff,
                     Metric.mem_closedBall, dist_zero_right,
                     Metric.mem_ball, and_imp]
          intro x₃ hyp_x₃ dist_hyp
          have : x₃ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2) := by
            apply Set.mem_inter
            · rw [Metric.mem_closedBall, dist_zero_right]; exact hyp_x₃
            · rw [Metric.mem_ball]; exact dist_hyp
          exact Z x₃ this

  · use Metric.ball 0 R
    constructor
    · exact Metric.isOpen_ball
    · constructor
      · simp only [ball_eq, sub_zero, Set.mem_setOf_eq]
        simp only [Metric.mem_closedBall, dist_zero_right] at x_hyp
        apply lt_of_le_of_ne x_hyp
        · rw [ne_eq]; exact h
      · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R = Metric.ball (0 : ℂ) R := by
          apply Set.inter_eq_self_of_subset_right
          rw [Metric.mem_closedBall, dist_zero_right] at x_hyp
          exact Metric.ball_subset_closedBall
        rw [si]
        apply AnalyticOn.divRemovableZero
        · apply Metric.ball_mem_nhds; positivity
        · exact zero
        · apply Metric.isOpen_ball
        · apply AnalyticOn.mono analytic Metric.ball_subset_closedBall

/-- Given `f` we define the `schwarzQuotient` as `(divRemovableZero f z) / (2 * M - f z)`. -/
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) : ℂ → ℂ :=
  fun z ↦ (divRemovableZero f z) / (2 * M - f z)

/-- Given `f` analytic in `|z| ≤ R`, the Schwartz quotient
`(f(z) / z) / (2 * M - f(z))` is analytic in `|z| ≤ R` provided
that `f 0 = 0` and `2 * M - f z ≠ 0` on the entire domain `|z| ≤ R` -/
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ} (M : ℝ)
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) : AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) := by

  have sInNhds0 : Metric.closedBall 0 R ∈ nhds 0 := by
    apply Metric.closedBall_mem_nhds; exact Rpos

  exact AnalyticOn.div
    (AnalyticOn.divRemovableZero_closedBall Rpos analytic zero)
    (AnalyticOn.sub (analyticOn_const) analytic) nonzero

/-- If `x.re ≤ M` then `|x| ≤ |2 * M - x|` -/
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ} {x : ℂ}
    (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) : ‖x‖ ≤ ‖2 * M - x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, mul_re, re_ofNat, ofReal_re,
             im_ofNat, ofReal_im, mul_zero, sub_zero,
             sub_im, mul_im, zero_mul, add_zero, zero_sub,
             mul_neg, neg_mul, neg_neg, add_le_add_iff_right]
  ring_nf
  simp only [add_comm (-(x.re * M * 4)) (x.re ^ 2), sq M,
             add_assoc, le_add_iff_nonneg_right (x.re ^ 2),
             le_neg_add_iff_add_le, add_zero, Nat.ofNat_pos,
             mul_le_mul_iff_left₀, mul_le_mul_iff_left₀ Mpos]
  exact hyp_re_x

/-- Specialization of the maximum modulus to `|z| ≤ R`: if `f` is analytic
on `|z| ≤ R` and `|f z| ≤ C` for all `|z| = R` then for any `r ≤ R` and
for all `|z| ≤ r`, `|f z| ≤ C` -/
lemma AnalyticOn.norm_le_of_norm_le_on_sphere {f : ℂ → ℂ} {C R r : ℝ}
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (hyp_r : r ≤ R) (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (w : ℂ) (wInS : w ∈ Metric.closedBall 0 r) : ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) (Metric.isBounded_closedBall)
  · apply DifferentiableOn.diffContOnCl; rw [Metric.closure_closedBall]
    apply AnalyticOn.differentiableOn
    apply AnalyticOn.mono (𝕜 := ℂ) analytic
    · apply Metric.closedBall_subset_closedBall; linarith
  · rw [frontier_closedBall']; exact cond
  · rw [Metric.closure_closedBall]; exact wInS

/-- The Borel-Caratheodory theorem (first version): If `f` is analytic in `|z| ≤ R`
and `f 0 = 0` and `(f z).re ≤ M` for all `|z| ≤ R` then for any
`0 < r < R` and all `|z| ≤ r` we have `|f(z)| ≤ 2 * M * r / (R - r)` -/
theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
    : ‖f z‖ ≤ (2 * M * r) / (R - r) := by

  have zInSFunc : ∀ r ≤ R, ∀ z ∈ Metric.sphere (0 : ℂ) r, z ∈ Metric.closedBall (0 : ℂ) R := by
    intro r hyp_r z hyp_z
    apply Set.mem_of_mem_of_subset (s := Metric.sphere 0 r) hyp_z
    · calc Metric.sphere (0 : ℂ) r
        _ ⊆ Metric.closedBall (0 : ℂ) r := Metric.sphere_subset_closedBall
        _ ⊆ Metric.closedBall (0 : ℂ) R := Metric.closedBall_subset_closedBall hyp_r

  have fPosAll : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.mul_re, Complex.re_ofNat,
          Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im,
          mul_zero, sub_zero, sub_pos]
      linarith [realPartBounded z zInS])

  have schwartzQuotientBounded : ∀ z ∈ Metric.sphere 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by linarith)
    have zInS : z ∈ Metric.closedBall 0 R := zInSFunc R (by rfl) z hyp_z
    rw [mem_sphere_iff_norm, sub_zero] at hyp_z

    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by
        simp only [Complex.norm_div, divRemovableZero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0;
        · simp only [h, zero_div, div_zero, le_refl]
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (Complex.norm_le_norm_two_mul_sub_of_re_le Mpos (realPartBounded z zInS))
      _ ≤ (1 / ‖z‖) := by
        by_cases h : ‖f z‖ = 0
        · rw [h, zero_div, div_zero, one_div, inv_nonneg]; apply norm_nonneg
        · rw [div_div, mul_comm, ← div_div, div_self]; exact h
      _ = 1 / R := by rw [hyp_z]

  have maxMod : ∀ z ∈ Metric.closedBall 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    exact AnalyticOn.norm_le_of_norm_le_on_sphere
      (AnalyticOn.schwartzQuotient M Rpos analytic fPosAll zeroAtZero)
      (by rfl) schwartzQuotientBounded

  have boundForF : ∀ r < R, 0 < r → ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R := zInSFunc r (by linarith) z (zOnR)
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by rw [← norm_pos_iff]; linarith
    rw [divRemovableZero_of_ne_zero f U] at this
    simp only [Complex.norm_div, one_div] at this
    have U : 0 < r * ‖2 * M - f z‖ := by
      simp only [r_pos, mul_pos_iff_of_pos_left, norm_pos_iff,
                 ne_eq, fPosAll z zInS, not_false_eq_true]
    rw [zOnR, div_div, div_le_iff₀' U] at this
    have U0 : ‖f z‖ ≤ 2 * M * r / R + ( r / R ) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          gcongr; apply norm_sub_le (E := ℂ) ((2 : ℂ) * ↑M) (f z)
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          have U : ‖(2 : ℂ) * M‖ = 2 * M := by
            simp only [Complex.norm_mul, Complex.norm_ofNat,
                       Complex.norm_real, Real.norm_eq_abs,
                       mul_eq_mul_left_iff, abs_eq_self,
                       OfNat.ofNat_ne_zero, or_false]
            linarith
          rw [U]
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by ring_nf
    have U1 : ‖f z‖ - ‖f z‖ * (r * R⁻¹) = ‖f z‖ * (1 - r * R⁻¹) := by ring
    have U2 : (0 : ℝ) < 1 - r * R⁻¹ := by
      have U1 : 0 < R := by linarith
      have U : r * R⁻¹ < 1 := by simp only [← div_lt_one₀ U1] at hyp_r; exact hyp_r
      linarith
    have U3 : r * R⁻¹ * M * 2 / (1 - r * R⁻¹) = 2 * M * r / (R - r) := by
      have : R ≠ 0 := by linarith
      rw [← mul_div_mul_left (r * R⁻¹ * M * (2 : ℝ)) ((1 : ℝ) - r * R⁻¹) this ];
      ring_nf
      have U : R * r * R⁻¹ = r := by
        rw [mul_comm, ← mul_assoc, ← mul_comm R R⁻¹,
            CommGroupWithZero.mul_inv_cancel R this, one_mul]
      rw [U]

    rw [← sub_le_sub_iff_right ((r / R) * ‖f z‖)] at U0; ring_nf at U0
    rw [mul_assoc, U1, ← le_div_iff₀ U2, U3] at U0
    exact U0

  have maxBoundForF : ∀ r < R, 0 < r → ∀ z ∈ Metric.closedBall 0 r,
  ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r pos_r
    exact AnalyticOn.norm_le_of_norm_le_on_sphere analytic
      (by linarith) (boundForF r hyp_r pos_r)

  by_cases pos_r : r = 0
  · have U : z = 0 := by
      rw [pos_r, Metric.closedBall_zero, Set.mem_singleton_iff] at hyp_z
      exact hyp_z
    rw [U, pos_r]; rw [mul_zero, sub_zero, zero_div, norm_le_zero_iff]; exact zeroAtZero
  · have U : 0 ≤ r := by
      rw [mem_closedBall_iff_norm, sub_zero] at hyp_z; linarith [norm_nonneg z]
    exact maxBoundForF r (by linarith)
      (by
        apply lt_of_le_of_ne U
        · rw [ne_eq, eq_comm]; exact pos_r) z hyp_z

/-- The Borel-Caratheodory theorem (second version): If `f` is analytic in `|z| ≤ R`
and `(f z).re ≤ M` for all `|z| ≤ R` then for any `0 < r < R` and all
`|z| ≤ r` we have `|f(z)| ≤ 2 * M * r / (R - r) + |f 0| * (R + r) / (R - r) -/
theorem borelCaratheodory_closedBall' {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (Mpos : 0 < M) (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
    : ‖f z‖ ≤ (2 * M * r) / (R - r) + ‖f 0‖ * (R + r) / (R - r) := by
  have Z : ‖f z - f 0‖ ≤ (2 * (M + ‖f 0‖) * r) / (R - r) := by
    apply borelCaratheodory_closedBall (f := fun z ↦ f z - f 0)
    · exact Rpos
    · apply AnalyticOn.sub analytic analyticOn_const
    · rw [sub_self]
    · positivity
    · intro z hyp_z
      calc (f z - f 0).re
        _ ≤ (f z).re + (- (f 0)).re := by
          rw [Complex.sub_re, Complex.neg_re, le_add_neg_iff_add_le, sub_add_cancel]
        _ ≤ M + (- (f 0)).re := by gcongr; apply realPartBounded; exact hyp_z
        _ ≤ M + ‖- (f 0)‖ := by gcongr; apply Complex.re_le_norm
        _ = M + ‖f 0‖ := by rw [norm_neg]
    · exact hyp_r
    · exact hyp_z

  have T : R - r ≠ 0 := by linarith

  calc ‖f z‖
    _ ≤ ‖f z - f 0‖ + ‖f 0‖ := by apply norm_le_norm_sub_add
    _ ≤ 2 * (M + ‖f 0‖) * r / (R - r) + ‖f 0‖ := by gcongr
    _ = 2 * (M + ‖f 0‖) * r / (R - r) + ‖f 0‖ * 1 := by rw [mul_one]
    _ = 2 * (M + ‖f 0‖) * r / (R - r) + ‖f 0‖ * ((R - r) / (R - r)) := by congr; rw [← div_self T]
    _ = 2 * M * r / (R - r) + ‖f 0‖ * (R + r) / (R - r) := by ring_nf
