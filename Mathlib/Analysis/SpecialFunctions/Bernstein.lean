/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : Fin (n+1), (n.choose k * x^k * (1-x)^(n-k)) • f (k/n : ℝ)
```
for a continuous function `f : C([0,1], E)` taking values in a real normed space
converge uniformly to `f` as `n` tends to infinity.

Our proof follows [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D.
The original proof, due to [Bernstein](bernstein1912) in 1912, is probabilistic,
and relies on Bernoulli's theorem,
which gives bounds for how quickly the observed frequencies in a
Bernoulli trial approach the underlying probability.

The proof here does not directly rely on Bernoulli's theorem,
but can also be given a probabilistic account.
* Consider a weighted coin which with probability `x` produces heads,
  and with probability `1-x` produces tails.
* The value of `bernstein n k x` is the probability that
  such a coin gives exactly `k` heads in a sequence of `n` tosses.
* If such an appearance of `k` heads results in a payoff of `f(k / n)`,
  the `n`-th Bernstein approximation for `f` evaluated at `x` is the expected payoff.
* The main estimate in the proof bounds the probability that
  the observed frequency of heads differs from `x` by more than some `δ`,
  obtaining a bound of `(4 * n * δ^2)⁻¹`, irrespective of `x`.
* This ensures that for `n` large, the Bernstein approximation is (uniformly) close to the
  payoff function `f`.

(You don't need to think in these terms to follow the proof below: it's a giant `calc` block!)

This result proves Weierstrass' theorem that polynomials are dense in `C([0,1], ℝ)`,
although we defer an abstract statement of this until later.
-/

noncomputable section

open scoped BoundedContinuousFunction unitInterval

/-- The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I

theorem bernstein_apply (n ν : ℕ) (x : I) :
    bernstein n ν x = (n.choose ν : ℝ) * (x : ℝ) ^ ν * (1 - (x : ℝ)) ^ (n - ν) := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  simp

@[simp]
theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [bernstein_apply]
  have h₁ : (0 : ℝ) ≤ x := by unit_interval
  have h₂ : (0 : ℝ) ≤ 1 - x := by unit_interval
  positivity

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension of the `positivity` tactic for Bernstein polynomials: they are always non-negative. -/
@[positivity DFunLike.coe (bernstein _ _) _]
def evalBernstein : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _coe (.app (.app _ n) ν)) x ← whnfR e | throwError "not bernstein polynomial"
  let p ← mkAppOptM ``bernstein_nonneg #[n, ν, x]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

/-!
We now give a slight reformulation of `bernsteinPolynomial.variance`.
-/


namespace bernstein

/-- Send `k : Fin (n+1)` to the equally spaced points `k/n` in the unit interval.
-/
def z {n : ℕ} (k : Fin (n + 1)) : I :=
  ⟨(k : ℝ) / n, by simp [div_nonneg, div_le_one_of_le₀, k.is_le]⟩

local postfix:90 "/ₙ" => z

@[simp] lemma z_zero {n : ℕ} : (0 : Fin (n + 1))/ₙ = 0 := by simp [z]
@[simp] lemma z_last {n : ℕ} (hn : n ≠ 0) : .last n/ₙ = 1 := by simp [z, hn]

@[simp]
theorem probability (n : ℕ) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum ℝ n
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  simp? [map_sum, Finset.sum_range] at this says
    simp only [Finset.sum_range, map_sum, Polynomial.coe_aeval_eq_eval, Polynomial.eval_one] at this
  exact this

theorem variance {n : ℕ} (hn : n ≠ 0) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = (x : ℝ) * (1 - x) / n := by
  convert congr(Polynomial.aeval (x : ℝ) $(bernsteinPolynomial.variance ℝ n) / n ^ 2) using 1 <;>
    field_simp [z, ← Finset.sum_div, bernstein_apply, Finset.sum_range, bernsteinPolynomial] <;>
      ring_nf

end bernstein

open bernstein

local postfix:1024 "/ₙ" => z

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, bernstein n k x • f (k/n)`.
-/
def bernsteinApproximation [NormedSpace ℝ E] (n : ℕ) (f : C(I, E)) : C(I, E) :=
  ∑ k : Fin (n + 1), bernstein n k • .const _ (f k/ₙ)

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, E)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `Fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `‖f x - f y‖ < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/

namespace bernsteinApproximation

section

variable [NormedSpace ℝ E]

theorem apply (n : ℕ) (f : C(I, E)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f k/ₙ := by
  simp [bernsteinApproximation]

@[simp]
theorem apply_zero (n : ℕ) (f : C(I, E)) : bernsteinApproximation n f 0 = f 0 := by
  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]

@[simp]
theorem apply_one {n : ℕ} (hn : n ≠ 0) (f : C(I, E)) : bernsteinApproximation n f 1 = f 1 := by
  simp [apply, Fin.sum_univ_castSucc, bernstein_apply, hn, Nat.sub_eq_zero_iff_le]

end

/-- The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, E)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)

theorem δ_pos {f : C(I, E)} {ε : ℝ} {h : 0 < ε} : 0 < δ f ε h :=
  f.modulus_pos

/-- The set of points `k` so `k/n` is within `δ` of `x`.
-/
def S (f : C(I, E)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Fin (n + 1)) :=
  {k : Fin (n + 1) | dist k/ₙ x < δ f ε h}.toFinset

/-- If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
theorem lt_of_mem_S {f : C(I, E)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ S f ε h n x) : ‖f k/ₙ - f x‖ < ε / 2 := by
  rw [← dist_eq_norm]
  apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
  simpa [S] using m

/-- If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
theorem le_of_mem_S_compl {f : C(I, E)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ (S f ε h n x)ᶜ) : (1 : ℝ) ≤ δ f ε h ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 := by
  simp only [Finset.mem_compl, not_lt, Set.mem_toFinset, Set.mem_setOf_eq, S] at m
  rw [zpow_neg, ← div_eq_inv_mul, zpow_two, ← pow_two, one_le_div (pow_pos δ_pos 2), sq_le_sq,
    abs_of_pos δ_pos]
  rwa [dist_comm] at m

end bernsteinApproximation

open bernsteinApproximation

open BoundedContinuousFunction

open Filter

open scoped Topology

/-- The Bernstein approximations
```
∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
theorem bernsteinApproximation_uniform [NormedSpace ℝ E] (f : C(I, E)) :
    Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) := by
  simp only [Metric.nhds_basis_ball.tendsto_right_iff, Metric.mem_ball, dist_eq_norm]
  intro ε h
  let δ := δ f ε h
  have nhds_zero := tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖ * δ ^ (-2 : ℤ))
  filter_upwards [nhds_zero.eventually_lt_const (half_pos h), eventually_ne_atTop 0]
    with n nh hn₀
  -- As `[0,1]` is compact, it suffices to check the inequality pointwise.
  rw [ContinuousMap.norm_lt_iff _ h]
  intro x
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  let S := S f ε h n x
  calc
    ‖(bernsteinApproximation n f - f) x‖
      = ‖∑ k : Fin (n + 1), bernstein n k x • (f k/ₙ - f x)‖ := by
      simp [bernsteinApproximation.apply, smul_sub, ← Finset.sum_smul]
    _ ≤ ∑ k : Fin (n + 1), ‖bernstein n k x • (f k/ₙ - f x)‖ := norm_sum_le _ _
    _ = ∑ k : Fin (n + 1), bernstein n k x * ‖f k/ₙ - f x‖ := by
      simp only [norm_smul, Real.norm_of_nonneg bernstein_nonneg]
    _ = (∑ k ∈ S,  bernstein n k x * ‖f k/ₙ - f x‖) + ∑ k ∈ Sᶜ, bernstein n k x * ‖f k/ₙ - f x‖ :=
      (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt ?_ ?_
    _ = ε := add_halves ε
  · -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
    -- quickly give us a bound.
    calc
      ∑ k ∈ S, bernstein n k x * ‖f k/ₙ - f x‖ ≤ ∑ k ∈ S, bernstein n k x * (ε / 2) := by
        gcongr with _ m
        exact (lt_of_mem_S m).le
      _ = ε / 2 * ∑ k ∈ S, bernstein n k x := by rw [mul_comm, Finset.sum_mul]
      -- In this step we increase the sum over `S` back to a sum over all of `Fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      _ ≤ ε / 2 * ∑ k : Fin (n + 1), bernstein n k x := by gcongr; exact S.subset_univ
      _ = ε / 2 := by rw [bernstein.probability, mul_one]
  · -- We now turn to working on `Sᶜ`: we control the difference term just using `‖f‖`,
    -- and then insert a `δ^(-2) * (x - k/n)^2` factor
    -- (which is at least one because we are not in `S`).
    calc
      ∑ k ∈ Sᶜ, bernstein n k x * ‖f k/ₙ - f x‖ ≤ ∑ k ∈ Sᶜ, 2 * ‖f‖ * bernstein n k x := by
        simp only [mul_comm (bernstein n _ x), ← dist_eq_norm]
        gcongr
        apply f.dist_le_two_norm
      _ = 2 * ‖f‖ * ∑ k ∈ Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ 2 * ‖f‖ * ∑ k ∈ Sᶜ, δ ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        gcongr with _ m
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        exact le_of_mem_S_compl m
      -- Again enlarging the sum from `Sᶜ` to all of `Fin (n+1)`
      _ ≤ 2 * ‖f‖ * ∑ k : Fin (n + 1), δ ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        gcongr; exact Sᶜ.subset_univ
      _ = 2 * ‖f‖ * δ ^ (-2 : ℤ) * ∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        simp only [mul_assoc, Finset.mul_sum]
      -- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
      _ = 2 * ‖f‖ * δ ^ (-2 : ℤ) * x * (1 - x) / n := by rw [variance hn₀]; ring
      _ ≤ 2 * ‖f‖ * δ ^ (-2 : ℤ) * 1 * 1 / n := by gcongr <;> unit_interval
      _ < ε / 2 := by simp only [mul_one]; exact nh
