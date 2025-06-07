/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.AdaptationNote

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `Real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-Real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarithm, derivative
-/


open Filter Finset Set

open scoped Topology ContDiff

namespace Real

variable {x : ℝ}

theorem hasStrictDerivAt_log_of_pos (hx : 0 < x) : HasStrictDerivAt log x⁻¹ x := by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
        (ne_of_gt <| exp_pos _) <|
      Eventually.mono (lt_mem_nhds hx) @exp_log
  rwa [exp_log hx] at this

theorem hasStrictDerivAt_log (hx : x ≠ 0) : HasStrictDerivAt log x⁻¹ x := by
  rcases hx.lt_or_gt with hx | hx
  · convert (hasStrictDerivAt_log_of_pos (neg_pos.mpr hx)).comp x (hasStrictDerivAt_neg x) using 1
    · ext y; exact (log_neg_eq_log y).symm
    · field_simp [hx.ne]
  · exact hasStrictDerivAt_log_of_pos hx

theorem hasDerivAt_log (hx : x ≠ 0) : HasDerivAt log x⁻¹ x :=
  (hasStrictDerivAt_log hx).hasDerivAt

@[fun_prop] theorem differentiableAt_log (hx : x ≠ 0) : DifferentiableAt ℝ log x :=
  (hasDerivAt_log hx).differentiableAt

theorem differentiableOn_log : DifferentiableOn ℝ log {0}ᶜ := fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

@[simp]
theorem differentiableAt_log_iff : DifferentiableAt ℝ log x ↔ x ≠ 0 :=
  ⟨fun h => continuousAt_log_iff.1 h.continuousAt, differentiableAt_log⟩

theorem deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
  if hx : x = 0 then by
    rw [deriv_zero_of_not_differentiableAt (differentiableAt_log_iff.not_left.2 hx), hx, inv_zero]
  else (hasDerivAt_log hx).deriv

@[simp]
theorem deriv_log' : deriv log = Inv.inv :=
  funext deriv_log

theorem contDiffAt_log {n : WithTop ℕ∞} {x : ℝ} : ContDiffAt ℝ n log x ↔ x ≠ 0 := by
  refine ⟨fun h ↦ continuousAt_log_iff.1 h.continuousAt, fun hx ↦ ?_⟩
  have A y (hy : 0 < y) : ContDiffAt ℝ n log y := by
    apply expPartialHomeomorph.contDiffAt_symm_deriv (f₀' := y) hy.ne' (by simpa)
    · convert hasDerivAt_exp (log y)
      rw [exp_log hy]
    · exact analyticAt_rexp.contDiffAt
  rcases hx.lt_or_gt with hx | hx
  · have : ContDiffAt ℝ n (log ∘ (fun y ↦ -y)) x := by
      apply ContDiffAt.comp
      apply A _ (Left.neg_pos_iff.mpr hx)
      apply contDiffAt_id.neg
    convert this
    ext x
    simp
  · exact A x hx

@[fun_prop]
theorem contDiffOn_log {n : WithTop ℕ∞} : ContDiffOn ℝ n log {0}ᶜ := by
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff] at hx
  exact (contDiffAt_log.2 hx).contDiffWithinAt

end Real

section LogDifferentiable

open Real

section deriv

variable {f : ℝ → ℝ} {x f' : ℝ} {s : Set ℝ}

theorem HasDerivWithinAt.log (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => log (f y)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (hasDerivAt_log hx).comp_hasDerivWithinAt x hf

theorem HasDerivAt.log (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [← hasDerivWithinAt_univ] at *
  exact hf.log hx

theorem HasStrictDerivAt.log (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun y => log (f y)) (f' / f x) x := by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log hx).comp x hf

theorem derivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => log (f x)) s x = derivWithin f s x / f x :=
  (hf.hasDerivWithinAt.log hx).derivWithin hxs

@[simp]
theorem deriv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    deriv (fun x => log (f x)) x = deriv f x / f x :=
  (hf.hasDerivAt.log hx).deriv

/-- The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differentiable and
`f x  ≠ 0`. -/
lemma Real.deriv_log_comp_eq_logDeriv {f : ℝ → ℝ} {x : ℝ} (h₁ : DifferentiableAt ℝ f x)
    (h₂ : f x ≠ 0) : deriv (log ∘ f) x = logDeriv f x := by
  simp only [ne_eq, logDeriv, Pi.div_apply, ← deriv.log h₁ h₂, Function.comp_def]

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : Set E}

theorem HasFDerivWithinAt.log (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFDerivWithinAt (fun x => log (f x)) ((f x)⁻¹ • f') s x :=
  (hasDerivAt_log hx).comp_hasFDerivWithinAt x hf

theorem HasFDerivAt.log (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (hasDerivAt_log hx).comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.log (hf : HasStrictFDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log hx).comp_hasStrictFDerivAt x hf

theorem DifferentiableWithinAt.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun x => log (f x)) s x :=
  (hf.hasFDerivWithinAt.log hx).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun x => log (f x)) x :=
  (hf.hasFDerivAt.log hx).differentiableAt

@[fun_prop]
theorem ContDiffAt.log {n} (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => log (f x)) x :=
  (contDiffAt_log.2 hx).comp x hf

@[fun_prop]
theorem ContDiffWithinAt.log {n} (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => log (f x)) s x :=
  (contDiffAt_log.2 hx).comp_contDiffWithinAt x hf

@[fun_prop]
theorem ContDiffOn.log {n} (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => log (f x)) s := fun x hx => (hf x hx).log (hs x hx)

@[fun_prop]
theorem ContDiff.log {n} (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => log (f x) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.log (h x)

@[fun_prop]
theorem DifferentiableOn.log (hf : DifferentiableOn ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun x => log (f x)) s := fun x h => (hf x h).log (hx x h)

@[simp, fun_prop]
theorem Differentiable.log (hf : Differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun x => log (f x) := fun x => (hf x).log (hx x)

theorem fderivWithin.log (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => log (f x)) s x = (f x)⁻¹ • fderivWithin ℝ f s x :=
  (hf.hasFDerivWithinAt.log hx).fderivWithin hxs

@[simp]
theorem fderiv.log (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
  (hf.hasFDerivAt.log hx).fderiv

end fderiv

end LogDifferentiable

namespace Real

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `hasSum_pow_div_log_of_abs_lt_1`.

TODO: use one of generic theorems about Taylor's series to prove this estimate.
-/
theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |(∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|) := by
  /- For the proof, we show that the derivative of the function to be estimated is small,
    and then apply the mean value inequality. -/
  let F : ℝ → ℝ := fun x => (∑ i ∈ range n, x ^ (i + 1) / (i + 1)) + log (1 - x)
  let F' : ℝ → ℝ := fun x ↦ -x ^ n / (1 - x)
  -- Porting note: In `mathlib3`, the proof used `deriv`/`DifferentiableAt`. `simp` failed to
  -- compute `deriv`, so I changed the proof to use `HasDerivAt` instead
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, HasDerivAt F (F' y) y := fun y hy ↦ by
    have : HasDerivAt F ((∑ i ∈ range n, ↑(i + 1) * y ^ i / (↑i + 1)) + (-1) / (1 - y)) y :=
      .add (.sum fun i _ ↦ (hasDerivAt_pow (i + 1) y).div_const ((i : ℝ) + 1))
        (((hasDerivAt_id y).const_sub _).log <| sub_ne_zero.2 hy.2.ne')
    convert this using 1
    calc
      -y ^ n / (1 - y) = ∑ i ∈ Finset.range n, y ^ i + -1 / (1 - y) := by
        field_simp [geom_sum_eq hy.2.ne, sub_ne_zero.2 hy.2.ne, sub_ne_zero.2 hy.2.ne']
        ring
      _ = ∑ i ∈ Finset.range n, ↑(i + 1) * y ^ i / (↑i + 1) + -1 / (1 - y) := by
        congr with i
        rw [Nat.cast_succ, mul_div_cancel_left₀ _ (Nat.cast_add_one_pos i).ne']
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-|x|) |x|, |F' y| ≤ |x| ^ n / (1 - |x|) := fun y hy ↦
    calc
      |F' y| = |y| ^ n / |1 - y| := by simp [F', abs_div]
      _ ≤ |x| ^ n / (1 - |x|) := by
        have : |y| ≤ |x| := abs_le.2 hy
        have : 1 - |x| ≤ |1 - y| := le_trans (by linarith [hy.2]) (le_abs_self _)
        gcongr
        exact sub_pos.2 h
  -- third step: apply the mean value inequality
  have C : ‖F x - F 0‖ ≤ |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy ↦ (A _ ?_).hasDerivWithinAt) B (convex_Icc _ _) ?_ ?_
    · exact Icc_subset_Ioo (neg_lt_neg h) h hy
    · simp
    · simp [le_abs_self x, neg_le.mp (neg_le_abs x)]
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, div_mul_eq_mul_div, pow_succ] using C

/-- Power series expansion of the logarithm around `1`. -/
theorem hasSum_pow_div_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / (n + 1)) (-log (1 - x)) := by
  rw [Summable.hasSum_iff_tendsto_nat]
  · show Tendsto (fun n : ℕ => ∑ i ∈ range n, x ^ (i + 1) / (i + 1)) atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    suffices Tendsto (fun t : ℕ => |x| ^ (t + 1) / (1 - |x|)) atTop (𝓝 (|x| * 0 / (1 - |x|))) by
      simpa
    simp only [pow_succ']
    refine (tendsto_const_nhds.mul ?_).div_const _
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg _) h
  show Summable fun n : ℕ => x ^ (n + 1) / (n + 1)
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / (i + 1)‖ = |x| ^ (i + 1) / (i + 1) := by
      have : (0 : ℝ) ≤ i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this]
    _ ≤ |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      exact i.cast_nonneg
    _ ≤ |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h)

/-- Power series expansion of `log(1 + x) - log(1 - x)` for `|x| < 1`. -/
theorem hasSum_log_sub_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1))
      (log (1 + x) - log (1 - x)) := by
  set term := fun n : ℕ => -1 * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + x ^ (n + 1) / (n + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : ℕ => 2 * (1 / (2 * k + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul, Set.mem_setOf_eq, ← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm, neg_one_mul, neg_add_cancel]

/-- Expansion of `log (1 + a⁻¹)` as a series in powers of `1 / (2 * a + 1)`. -/
theorem hasSum_log_one_add_inv {a : ℝ} (h : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (log (1 + a⁻¹)) := by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos, div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    field_simp
    linarith
  · field_simp
    linarith
  · field_simp

/-- Expansion of `log (1 + a)` as a series in powers of `a / (a + 2)`. -/
theorem hasSum_log_one_add {a : ℝ} (h : 0 ≤ a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * k + 1)) * (a / (a + 2)) ^ (2 * k + 1))
      (log (1 + a)) := by
  obtain (rfl | ha0) := eq_or_ne a 0
  · simp [hasSum_zero]
  · convert hasSum_log_one_add_inv (inv_pos.mpr (lt_of_le_of_ne h ha0.symm)) using 4
    all_goals field_simp [add_comm]

lemma le_log_one_add_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 2 * x / (x + 2) ≤ log (1 + x) := by
  convert le_hasSum (hasSum_log_one_add hx) 0 (by intros; positivity) using 1
  field_simp

lemma lt_log_one_add_of_pos {x : ℝ} (hx : 0 < x) : 2 * x / (x + 2) < log (1 + x) := by
  convert lt_hasSum (hasSum_log_one_add hx.le) 0 (by intros; positivity)
    1 (by positivity) (by positivity) using 1
  field_simp

end Real
