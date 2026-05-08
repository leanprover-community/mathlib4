/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Polynomial.Module.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Taylor's theorem

This file defines the Taylor polynomial of a real function `f : ℝ → E`,
where `E` is a normed vector space over `ℝ` and proves Taylor's theorem,
which states that if `f` is sufficiently smooth, then
`f` can be approximated by the Taylor polynomial up to an explicit error term.

## Main definitions

* `taylorCoeffWithin`: the Taylor coefficient using `iteratedDerivWithin`
* `taylorWithin`: the Taylor polynomial using `iteratedDerivWithin`

## Main statements

* `taylor_tendsto`: Taylor's theorem as a limit
* `taylor_isLittleO`: Taylor's theorem using little-o notation
* `taylor_mean_remainder`: Taylor's theorem with the general form of the remainder term
* `taylor_mean_remainder_lagrange`: Taylor's theorem with the Lagrange remainder
* `taylor_mean_remainder_cauchy`: Taylor's theorem with the Cauchy remainder
* `exists_taylor_mean_remainder_bound`: Taylor's theorem for vector-valued functions with a
  polynomial bound on the remainder
* `taylor_integral_remainder_of_absolutelyContinuous`,
  `taylor_integral_remainder`: Taylor's theorem with the integral form of the
  remainder

## TODO

* Generalization to higher dimensions

## Tags

Taylor polynomial, Taylor's theorem
-/

@[expose] public section


open scoped Interval Topology Nat

open Set

variable {𝕜 E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `k`th coefficient of the Taylor polynomial. -/
noncomputable def taylorCoeffWithin (f : ℝ → E) (k : ℕ) (s : Set ℝ) (x₀ : ℝ) : E :=
  (k ! : ℝ)⁻¹ • iteratedDerivWithin k f s x₀

/-- The Taylor polynomial with derivatives inside of a set `s`.

The Taylor polynomial is given by
$$∑_{k=0}^n \frac{(x - x₀)^k}{k!} f^{(k)}(x₀),$$
where $f^{(k)}(x₀)$ denotes the iterated derivative in the set `s`. -/
noncomputable def taylorWithin (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) : PolynomialModule ℝ E :=
  (Finset.range (n + 1)).sum fun k =>
    PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ k (taylorCoeffWithin f k s x₀))

/-- The Taylor polynomial with derivatives inside of a set `s` considered as a function `ℝ → E` -/
noncomputable def taylorWithinEval (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) : E :=
  PolynomialModule.eval x (taylorWithin f n s x₀)

theorem taylorWithin_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithin f (n + 1) s x₀ = taylorWithin f n s x₀ +
      PolynomialModule.comp (Polynomial.X - Polynomial.C x₀)
      (PolynomialModule.single ℝ (n + 1) (taylorCoeffWithin f (n + 1) s x₀)) := by
  dsimp only [taylorWithin]
  rw [Finset.sum_range_succ]

@[simp]
theorem taylorWithinEval_succ (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f (n + 1) s x₀ x = taylorWithinEval f n s x₀ x +
      (((n + 1 : ℝ) * n !)⁻¹ * (x - x₀) ^ (n + 1)) • iteratedDerivWithin (n + 1) f s x₀ := by
  simp_rw [taylorWithinEval, taylorWithin_succ, map_add, PolynomialModule.comp_eval]
  congr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    PolynomialModule.eval_single, mul_inv_rev]
  dsimp only [taylorCoeffWithin]
  rw [← mul_smul, mul_comm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    mul_inv_rev]

/-- The Taylor polynomial of order zero evaluates to `f x`. -/
@[simp]
theorem taylor_within_zero_eval (f : ℝ → E) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f 0 s x₀ x = f x₀ := by
  dsimp only [taylorWithinEval]
  dsimp only [taylorWithin]
  dsimp only [taylorCoeffWithin]
  simp

/-- Evaluating the Taylor polynomial at `x = x₀` yields `f x`. -/
@[simp]
theorem taylorWithinEval_self (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ : ℝ) :
    taylorWithinEval f n s x₀ x₀ = f x₀ := by
  induction n with
  | zero => exact taylor_within_zero_eval _ _ _ _
  | succ k hk => simp [hk]

theorem taylor_within_apply (f : ℝ → E) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * (x - x₀) ^ k) • iteratedDerivWithin k f s x₀ := by
  induction n with
  | zero => simp
  | succ k hk =>
    rw [taylorWithinEval_succ, Finset.sum_range_succ, hk]
    simp [Nat.factorial]

/-- If `f` is `n` times continuous differentiable on a set `s`, then the Taylor polynomial
  `taylorWithinEval f n s x₀ x` is continuous in `x₀`. -/
theorem continuousOn_taylorWithinEval {f : ℝ → E} {x : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (hf : ContDiffOn ℝ n f s) :
    ContinuousOn (fun t => taylorWithinEval f n s t x) s := by
  simp_rw [taylor_within_apply]
  refine continuousOn_finsetSum (Finset.range (n + 1)) fun i hi => ?_
  refine (continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).pow _)).smul ?_
  rw [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv hs] at hf
  simp only [Finset.mem_range] at hi
  refine hf.1 i ?_
  simp only [Nat.lt_succ_iff.mp hi]

/-- Helper lemma for calculating the derivative of the monomial that appears in Taylor
expansions. -/
theorem monomial_has_deriv_aux (t x : ℝ) (n : ℕ) :
    HasDerivAt (fun y => (x - y) ^ (n + 1)) (-(n + 1) * (x - t) ^ n) t := by
  simp_rw [sub_eq_neg_add]
  rw [← neg_one_mul, mul_comm (-1 : ℝ), mul_assoc, mul_comm (-1 : ℝ), ← mul_assoc]
  convert ((hasDerivAt_id t).neg.add_const x).pow (n + 1)
  simp only [Nat.cast_add, Nat.cast_one]

theorem hasDerivWithinAt_taylor_coeff_within {f : ℝ → E} {x y : ℝ} {k : ℕ} {s t : Set ℝ}
    (ht : UniqueDiffWithinAt ℝ t y) (hs : s ∈ 𝓝[t] y)
    (hf : DifferentiableWithinAt ℝ (iteratedDerivWithin (k + 1) f s) s y) :
    HasDerivWithinAt
      (fun z => (((k + 1 : ℝ) * k !)⁻¹ * (x - z) ^ (k + 1)) • iteratedDerivWithin (k + 1) f s z)
      ((((k + 1 : ℝ) * k !)⁻¹ * (x - y) ^ (k + 1)) • iteratedDerivWithin (k + 2) f s y -
        ((k ! : ℝ)⁻¹ * (x - y) ^ k) • iteratedDerivWithin (k + 1) f s y) t y := by
  replace hf :
    HasDerivWithinAt (iteratedDerivWithin (k + 1) f s) (iteratedDerivWithin (k + 2) f s y) t y := by
    convert (hf.mono_of_mem_nhdsWithin hs).hasDerivWithinAt using 1
    rw [iteratedDerivWithin_succ]
    exact (derivWithin_of_mem_nhdsWithin hs ht hf).symm
  have : HasDerivWithinAt (fun t => ((k + 1 : ℝ) * k !)⁻¹ * (x - t) ^ (k + 1))
      (-((k ! : ℝ)⁻¹ * (x - y) ^ k)) t y := by
    -- Commuting the factors:
    have : -((k ! : ℝ)⁻¹ * (x - y) ^ k) = ((k + 1 : ℝ) * k !)⁻¹ * (-(k + 1) * (x - y) ^ k) := by
      field
    rw [this]
    exact (monomial_has_deriv_aux y x _).hasDerivWithinAt.const_mul _
  convert this.smul hf using 1
  field_simp
  module

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for arbitrary sets -/
theorem hasDerivWithinAt_taylorWithinEval {f : ℝ → E} {x y : ℝ} {n : ℕ} {s s' : Set ℝ}
    (hs_unique : UniqueDiffOn ℝ s) (hs' : s' ∈ 𝓝[s] y)
    (hy : y ∈ s') (h : s' ⊆ s) (hf : ContDiffOn ℝ n f s)
    (hf' : DifferentiableWithinAt ℝ (iteratedDerivWithin n f s) s y) :
    HasDerivWithinAt (fun t => taylorWithinEval f n s t x)
      (((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f s y) s' y := by
  have hs'_unique : UniqueDiffWithinAt ℝ s' y :=
    UniqueDiffWithinAt.mono_nhds (hs_unique _ (h hy)) (nhdsWithin_le_iff.mpr hs')
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
      mul_one, zero_add, one_smul]
    simp only [iteratedDerivWithin_zero] at hf'
    rw [iteratedDerivWithin_one]
    exact hf'.hasDerivWithinAt.mono h
  | succ k hk =>
    simp_rw [Nat.add_succ, taylorWithinEval_succ]
    simp only [add_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have coe_lt_succ : (k : WithTop ℕ) < k.succ := Nat.cast_lt.2 k.lt_succ_self
    have hdiff : DifferentiableOn ℝ (iteratedDerivWithin k f s) s' :=
      (hf.differentiableOn_iteratedDerivWithin (mod_cast coe_lt_succ) hs_unique).mono h
    specialize hk hf.of_succ ((hdiff y hy).mono_of_mem_nhdsWithin hs')
    convert hk.add (hasDerivWithinAt_taylor_coeff_within hs'_unique
      (nhdsWithin_mono _ h self_mem_nhdsWithin) hf') using 1
    exact (add_sub_cancel _ _).symm

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for open intervals -/
theorem taylorWithinEval_hasDerivAt_Ioo {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ} (hx : a < b)
    (ht : t ∈ Ioo a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    HasDerivAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) t :=
  have h_nhds : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have h_nhds' : Ioo a b ∈ 𝓝[Icc a b] t := nhdsWithin_le_nhds h_nhds
  (hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx) h_nhds' ht
    Ioo_subset_Icc_self hf <| (hf' t ht).mono_of_mem_nhdsWithin h_nhds').hasDerivAt h_nhds

/-- Calculate the derivative of the Taylor polynomial with respect to `x₀`.

Version for closed intervals -/
theorem hasDerivWithinAt_taylorWithinEval_at_Icc {f : ℝ → E} {a b t : ℝ} (x : ℝ) {n : ℕ}
    (hx : a < b) (ht : t ∈ Icc a b) (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b)) :
    HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a b) t :=
  hasDerivWithinAt_taylorWithinEval (uniqueDiffOn_Icc hx)
    self_mem_nhdsWithin ht rfl.subset hf (hf' t ht)

/-- Calculate the derivative of the Taylor polynomial with respect to `x`. -/
theorem hasDerivAt_taylorWithinEval_succ {x₀ x : ℝ} {s : Set ℝ} (f : ℝ → E) (n : ℕ) :
    HasDerivAt (taylorWithinEval f (n + 1) s x₀)
      (taylorWithinEval (derivWithin f s) n s x₀ x) x := by
  change HasDerivAt (fun x ↦ taylorWithinEval f _ s x₀ x) _ _
  simp_rw [taylor_within_apply]
  have : ∀ (i : ℕ) {c : ℝ} {c' : E},
      HasDerivAt (fun x ↦ (c * (x - x₀) ^ i) • c') ((c * (i * (x - x₀) ^ (i - 1) * 1)) • c') x :=
    fun _ _ ↦ hasDerivAt_id _ |>.sub_const _ |>.pow _ |>.const_mul _ |>.smul_const _
  apply HasDerivAt.fun_sum (fun i _ => this i) |>.congr_deriv
  rw [Finset.sum_range_succ', Nat.cast_zero, zero_mul, zero_mul, mul_zero, zero_smul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [← iteratedDerivWithin_succ']
  congr 1
  simp [field, Nat.factorial_succ]

/-- **Taylor's theorem** using little-o notation. -/
theorem taylor_isLittleO {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    (fun x ↦ f x - taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ n := by
  induction n generalizing f with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]
    exact hf.continuousOn.continuousWithinAt hx₀s
  | succ n h =>
    rcases s.eq_singleton_or_nontrivial hx₀s with rfl | hs'
    · simp
    replace hs' := uniqueDiffOn_convex hs (hs.nontrivial_iff_nonempty_interior.1 hs')
    simp only [Nat.cast_add, Nat.cast_one] at hf
    convert Convex.isLittleO_pow_succ_real hs hx₀s ?_ (h (hf.derivWithin hs' le_rfl))
      (f := fun x ↦ f x - taylorWithinEval f (n + 1) s x₀ x) using 1
    · simp
    · intro x hx
      refine HasDerivWithinAt.sub ?_ (hasDerivAt_taylorWithinEval_succ f n).hasDerivWithinAt
      exact (hf.differentiableOn (by simp) _ hx).hasDerivWithinAt

theorem taylor_isLittleO_univ {f : ℝ → E} {x₀ : ℝ} {n : ℕ} (hf : ContDiff ℝ n f) :
    (fun x ↦ f x - taylorWithinEval f n univ x₀ x) =o[𝓝 x₀] fun x ↦ (x - x₀) ^ n := by
  simpa using taylor_isLittleO convex_univ (mem_univ x₀) hf.contDiffOn

/-- **Taylor's theorem** as a limit. -/
theorem taylor_tendsto {f : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    Filter.Tendsto (fun x ↦ ((x - x₀) ^ n)⁻¹ • (f x - taylorWithinEval f n s x₀ x))
      (𝓝[s] x₀) (𝓝 0) := by
  have h_isLittleO := (taylor_isLittleO hs hx₀s hf).norm_norm
  rw [Asymptotics.isLittleO_iff_tendsto] at h_isLittleO
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_smul, div_eq_inv_mul] using h_isLittleO
  · simp only [norm_pow, Real.norm_eq_abs, pow_eq_zero_iff', abs_eq_zero, ne_eq, norm_eq_zero,
      and_imp]
    intro x hx
    rw [sub_eq_zero] at hx
    simp [hx]

/-- **Taylor's theorem** as a limit. -/
theorem Real.taylor_tendsto {f : ℝ → ℝ} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s) (hf : ContDiffOn ℝ n f s) :
    Filter.Tendsto (fun x ↦ (f x - taylorWithinEval f n s x₀ x) / (x - x₀) ^ n)
      (𝓝[s] x₀) (𝓝 0) := by
  convert _root_.taylor_tendsto hs hx₀s hf using 2 with x
  simp [div_eq_inv_mul]


/-! ### Taylor's theorem with mean value type remainder estimate -/


/-- **Taylor's theorem** with the general mean value form of the remainder.

We assume that `f` is `n`-times continuously differentiable in the closed set `uIcc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`, and `g` is a differentiable function on
`uIoo x₀ x` and continuous on `uIcc x₀ x`. Then there exists an `x' ∈ uIoo x₀ x` such that
$$f(x) - (P_n f)(x₀, x) = \frac{(x - x')^n}{n!} \frac{g(x) - g(x₀)}{g' x'},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$. -/
theorem taylor_mean_remainder {f : ℝ → ℝ} {g g' : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x))
    (gcont : ContinuousOn g (uIcc x₀ x))
    (gdiff : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → HasDerivAt g (g' x_1) x_1)
    (g'_ne : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → g' x_1 ≠ 0) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x = ((x - x') ^ n / n ! *
      (g x - g x₀) / g' x') • iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' := by
  have hx₁ : min x₀ x < max x₀ x := by grind
  -- We apply the mean value theorem
  rcases exists_ratio_hasDerivAt_eq_ratio_slope (fun t => taylorWithinEval f n (uIcc x₀ x) t x)
      (fun t => ((n ! : ℝ)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t) hx₁
      (continuousOn_taylorWithinEval (uniqueDiffOn_Icc hx₁) hf)
      (fun _ hy => taylorWithinEval_hasDerivAt_Ioo x hx₁ hy hf hf')
    g g' gcont gdiff with ⟨y, hy, h⟩
  use y, hy
  -- The rest is simplifications and trivial calculations
  grind [uIoo, smul_eq_mul, taylorWithinEval_self]

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- **Taylor's theorem** with the Lagrange form of the remainder.

We assume that `f` is `n`-times continuously differentiable in the closed set `uIcc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`. Then there exists an `x' ∈ uIoo x₀ x` such
that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x₀)^{n+1}}{(n+1)!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_mean_remainder_lagrange {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have gcont : ContinuousOn (fun t : ℝ => (x - t) ^ (n + 1)) (uIcc x₀ x) := by fun_prop
  have xy_ne : ∀ y : ℝ, y ∈ uIoo x₀ x → (x - y) ^ n ≠ 0 := by grind [uIoo, pow_ne_zero]
  have hg' : ∀ y : ℝ, y ∈ uIoo x₀ x → -(↑n + 1) * (x - y) ^ n ≠ 0 := fun y hy =>
    mul_ne_zero (neg_ne_zero.mpr (Nat.cast_add_one_ne_zero n)) (xy_ne y hy)
  -- We apply the general theorem with g(t) = (x - t)^(n+1)
  rcases taylor_mean_remainder hx hf hf' gcont (fun y _ => monomial_has_deriv_aux y x _) hg' with
    ⟨y, hy, h⟩
  use y, hy
  simp only [sub_self, zero_pow, Ne, Nat.succ_ne_zero, not_false_iff, zero_sub, mul_neg] at h
  rw [h, neg_div, ← div_neg, neg_mul, neg_neg]
  simp [field, xy_ne y hy, Nat.factorial]

/-- A corollary of Taylor's theorem with the Lagrange form of the remainder. -/
lemma taylor_mean_remainder_lagrange_iteratedDeriv {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (uIcc x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / (n + 1)! := by
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_Icc (by grind)
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIcc x₀ x) := by
    refine hf.differentiableOn_iteratedDerivWithin ?_ hu
    norm_cast
    simp
  obtain ⟨x', h1, h2⟩ := taylor_mean_remainder_lagrange hx hf.of_succ (hd.mono Ioo_subset_Icc_self)
  use x', h1
  rw [h2, iteratedDeriv_eq_iteratedFDeriv, iteratedDerivWithin_eq_iteratedFDerivWithin,
    iteratedFDerivWithin_eq_iteratedFDeriv hu _ ⟨le_of_lt h1.1, le_of_lt h1.2⟩]
  exact hf.contDiffAt (Icc_mem_nhds_iff.2 h1)

/-- **Taylor's theorem** with the Cauchy form of the remainder.

We assume that `f` is `n`-times continuously differentiable on the closed set `uIcc x₀ x` and
`n+1`-times differentiable on the open set `uIoo x₀ x`. Then there exists an `x' ∈ uIoo x₀ x` such
that
$$f(x) - (P_n f)(x₀, x) = \frac{f^{(n+1)}(x') (x - x')^n (x-x₀)}{n!},$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_mean_remainder_cauchy {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ} (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (uIcc x₀ x)) (uIoo x₀ x)) :
    ∃ x' ∈ uIoo x₀ x, f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (uIcc x₀ x) x' * (x - x') ^ n / n ! * (x - x₀) := by
  have gcont : ContinuousOn id (uIcc x₀ x) := by fun_prop
  have gdiff : ∀ x_1 : ℝ, x_1 ∈ uIoo x₀ x → HasDerivAt id ((fun _ : ℝ => (1 : ℝ)) x_1) x_1 :=
    fun _ _ => hasDerivAt_id _
  -- We apply the general theorem with g = id
  rcases taylor_mean_remainder hx hf hf' gcont gdiff fun _ _ => by simp with ⟨y, hy, h⟩
  use y, hy
  rw [h]
  simp [field]

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
The difference of `f` and its `n`-th Taylor polynomial can be estimated by
`C * (x - a)^(n+1) / n!` where `C` is a bound for the `n+1`-th iterated derivative of `f`. -/
theorem taylor_mean_remainder_bound {f : ℝ → E} {a b C x : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) (hx : x ∈ Icc a b)
    (hC : ∀ y ∈ Icc a b, ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤ C) :
    ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) / n ! := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · rw [Icc_self, mem_singleton_iff] at hx
    simp [hx]
  -- The nth iterated derivative is differentiable
  have hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Icc a b) :=
    hf.differentiableOn_iteratedDerivWithin (mod_cast n.lt_succ_self)
      (uniqueDiffOn_Icc h)
  -- We can uniformly bound the derivative of the Taylor polynomial
  have h' : ∀ y ∈ Ico a x,
      ‖((n ! : ℝ)⁻¹ * (x - y) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) y‖ ≤
        (n ! : ℝ)⁻¹ * |x - a| ^ n * C := by
    rintro y ⟨hay, hyx⟩
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    · rw [abs_mul, abs_pow, abs_inv, Nat.abs_cast]
      gcongr
    -- Estimate the iterated derivative by `C`
    · exact hC y ⟨hay, hyx.le.trans hx.2⟩
  -- Apply the mean value theorem for vector-valued functions:
  have A : ∀ t ∈ Icc a x, HasDerivWithinAt (fun y => taylorWithinEval f n (Icc a b) y x)
      (((↑n !)⁻¹ * (x - t) ^ n) • iteratedDerivWithin (n + 1) f (Icc a b) t) (Icc a x) t := by
    intro t ht
    have I : Icc a x ⊆ Icc a b := Icc_subset_Icc_right hx.2
    exact (hasDerivWithinAt_taylorWithinEval_at_Icc x h (I ht) hf.of_succ hf').mono I
  have := norm_image_sub_le_of_norm_deriv_le_segment' A h' x (right_mem_Icc.2 hx.1)
  simp only [taylorWithinEval_self] at this
  refine this.trans_eq ?_
  -- The rest is a trivial calculation
  rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
  ring

/-- **Taylor's theorem** with a polynomial bound on the remainder

We assume that `f` is `n+1`-times continuously differentiable on the closed set `Icc a b`.
There exists a constant `C` such that for all `x ∈ Icc a b` the difference of `f` and its `n`-th
Taylor polynomial can be estimated by `C * (x - a)^(n+1)`. -/
theorem exists_taylor_mean_remainder_bound {f : ℝ → E} {a b : ℝ} {n : ℕ} (hab : a ≤ b)
    (hf : ContDiffOn ℝ (n + 1) f (Icc a b)) :
    ∃ C, ∀ x ∈ Icc a b, ‖f x - taylorWithinEval f n (Icc a b) a x‖ ≤ C * (x - a) ^ (n + 1) := by
  rcases eq_or_lt_of_le hab with (rfl | h)
  · refine ⟨0, fun x hx => ?_⟩
    have : x = a := by simpa [← le_antisymm_iff] using hx
    simp [← this]
  -- We estimate by the supremum of the norm of the iterated derivative
  let g : ℝ → ℝ := fun y => ‖iteratedDerivWithin (n + 1) f (Icc a b) y‖
  use SupSet.sSup (g '' Icc a b) / (n !)
  intro x hx
  rw [div_mul_eq_mul_div₀]
  refine taylor_mean_remainder_bound hab hf hx fun y => ?_
  exact (hf.continuousOn_iteratedDerivWithin rfl.le <| uniqueDiffOn_Icc h).norm.le_sSup_image_Icc

/-- **Taylor's theorem** with the Integral form of the remainder. This is an auxiliary theorem
which is used to prove the two useful versions `taylor_integral_remainder_of_absolutelyContinuous`
and `taylor_integral_remainder`.

We assume that for any `k ≤ n`, the following equation on integration by parts hold:
$$\int_{x_0}^x \frac{f^{(k+1)}(t) (x - t)^k}{k!} =
\frac{f^{(k)}(t) (x - t)^k}{k!} |_{x_0}^x -\int_{x_0}^x \frac{f^{(k)}(t) (x - t)^{k-1}}{(k-1)!}.$$
Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_integral_remainder_aux [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ∀ k ≤ n, let u := fun t ↦ (x - t) ^ k / k !;
      let v := fun t ↦ iteratedDerivWithin k f [[x₀, x]] t;
      ∫ (t : ℝ) in x₀..x, u t • deriv v t = u x • v x - u x₀ • v x₀ -
      ∫ (t : ℝ) in x₀..x, deriv u t • v t) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  induction n with
  | zero =>
    simp only [taylor_within_zero_eval, pow_zero, Nat.factorial_zero, Nat.cast_one, ne_eq,
      one_ne_zero, not_false_eq_true, div_self, zero_add, iteratedDerivWithin_one, one_smul]
    simp only [nonpos_iff_eq_zero, sub_self, deriv_div_const, forall_eq, pow_zero,
      Nat.factorial_zero, Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self,
      iteratedDerivWithin_zero, one_smul, deriv_const', div_one, zero_smul,
      intervalIntegral.integral_zero, sub_zero] at hf
    rw [← hf]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.volume.ae_ne x₀, MeasureTheory.volume.ae_ne x] with _ _ _ _
    grind [derivWithin_of_mem_nhds, Icc_mem_nhds, uIcc]
  | succ n ih =>
    have : UniqueDiffOn ℝ [[x₀, x]] := uniqueDiffOn_Icc (by grind)
    specialize ih (by grind)
    simp only [taylorWithinEval_succ, mul_inv_rev]
    rw [sub_add_eq_sub_sub, ih]
    simp only [Nat.factorial, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have := hf (n + 1) (by rfl)
    convert this.symm using 1
    · simp only [sub_self, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, zero_smul, zero_sub, deriv_div_const, Nat.factorial]
      apply fun (a b c d : F) (_ : b = c) (_ : a = -d) ↦ show a - b = -c - d by grind
      · grind
      · rw [← intervalIntegral.integral_neg]
        congr
        ext t
        rw [deriv_fun_pow (by fun_prop), deriv_const_sub, deriv_id'', ← neg_smul]
        congr
        field_simp
        grind
    · apply intervalIntegral.integral_congr_ae
      filter_upwards [MeasureTheory.volume.ae_ne x₀, MeasureTheory.volume.ae_ne x] with _ _ _ _
      rw [iteratedDerivWithin_succ]
      congr
      · rw [Nat.factorial]; grind
      · grind [derivWithin_of_mem_nhds, Icc_mem_nhds, uIcc]

/-- **Taylor's theorem** with the Integral form of the remainder.

We assume that `f` is `n`-times continuously differentiable on the closed set `uIcc x₀ x` and
its `n`-th derivative is absolutely continuous on `uIcc x₀ x`. Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_integral_remainder_of_absolutelyContinuous {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hf₁ : ContDiffOn ℝ n f (uIcc x₀ x))
    (hf₂ : AbsolutelyContinuousOnInterval (iteratedDerivWithin n f (uIcc x₀ x)) x₀ x) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) * iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  apply taylor_integral_remainder_aux
  intro k hk
  apply AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
  · apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  · rcases hk.eq_or_lt with rfl | hk
    · exact hf₂
    have : UniqueDiffOn ℝ [[x₀, x]] := uniqueDiffOn_Icc (by grind)
    replace hf₁ := hf₁.of_le (m := k.succ) (by norm_cast)
    grind [ContDiffOn.absolutelyContinuousOnInterval,
      contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin]

/-- **Taylor's theorem** with the Integral form of the remainder.

We assume that `f` is `n+1`-times continuously differentiable on the closed set `uIcc x₀ x`. Then
$$f(x) - (P_n f)(x₀, x) = \int_{x_0}^x \frac{f^{(n+1)}(t) (x - t)^n}{n!} dt,$$
where $P_n f$ denotes the Taylor polynomial of degree $n$ and $f^{(n+1)}$ is the $n+1$-th iterated
derivative. -/
theorem taylor_integral_remainder [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ → F} {x x₀ : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1 : ℕ) f (uIcc x₀ x)) :
    f x - taylorWithinEval f n (uIcc x₀ x) x₀ x =
      ∫ t in x₀..x, ((x - t) ^ n / n !) • iteratedDerivWithin (n + 1) f (uIcc x₀ x) t := by
  rcases eq_or_ne x₀ x with rfl | this
  · simp
  have : UniqueDiffOn ℝ [[x₀, x]] := uniqueDiffOn_Icc (by grind)
  apply taylor_integral_remainder_aux
  intro k hk
  apply intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivAt
    (u := fun t ↦ (x - t) ^ k / k !) (v := fun t ↦ iteratedDerivWithin k f (uIcc x₀ x) t)
  · fun_prop
  · exact hf.continuousOn_iteratedDerivWithin (by norm_cast; omega) this
  · intro t ht
    apply DifferentiableAt.hasDerivAt
    fun_prop
  · intro t ht
    refine DifferentiableOn.hasDerivAt (s := uIoo x₀ x) ?_ (by grind [Ioo_mem_nhds, uIoo])
    exact hf.differentiableOn_iteratedDerivWithin (by norm_cast; omega) this
      |>.mono (by grind [uIoo, uIcc])
  · apply ContinuousOn.intervalIntegrable
    fun_prop
  · apply IntervalIntegrable.congr_ae (f := iteratedDerivWithin (k + 1) f [[x₀, x]])
    · exact hf.continuousOn_iteratedDerivWithin (by norm_cast; omega) this |>.intervalIntegrable
    · rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by measurability)]
      filter_upwards [MeasureTheory.volume.ae_ne x₀, MeasureTheory.volume.ae_ne x] with _ _ _ _
      rw [iteratedDerivWithin_succ]
      grind [derivWithin_of_mem_nhds, Icc_mem_nhds, uIcc]
