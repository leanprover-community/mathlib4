/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Topology.ContinuousFunction.Polynomial
import Mathlib.Topology.ContinuousFunction.Compact

#align_import analysis.special_functions.bernstein from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

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

set_option linter.uppercaseLean3 false -- S

noncomputable section

open scoped Classical BigOperators BoundedContinuousFunction unitInterval

/-- The Bernstein polynomials, as continuous functions on `[0,1]`.
-/
def bernstein (n ν : ℕ) : C(I, ℝ) :=
  (bernsteinPolynomial ℝ n ν).toContinuousMapOn I
#align bernstein bernstein

@[simp]
theorem bernstein_apply (n ν : ℕ) (x : I) :
    bernstein n ν x = (n.choose ν : ℝ) * (x : ℝ) ^ ν * (1 - (x : ℝ)) ^ (n - ν) := by
  dsimp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, bernsteinPolynomial]
  -- ⊢ Polynomial.eval (↑x) (↑(Nat.choose n ν) * Polynomial.X ^ ν * (1 - Polynomial …
  simp
  -- 🎉 no goals
#align bernstein_apply bernstein_apply

theorem bernstein_nonneg {n ν : ℕ} {x : I} : 0 ≤ bernstein n ν x := by
  simp only [bernstein_apply]
  -- ⊢ 0 ≤ ↑(Nat.choose n ν) * ↑x ^ ν * (1 - ↑x) ^ (n - ν)
  have h₁ : (0:ℝ) ≤ x := by unit_interval
  -- ⊢ 0 ≤ ↑(Nat.choose n ν) * ↑x ^ ν * (1 - ↑x) ^ (n - ν)
  have h₂ : (0:ℝ) ≤ 1 - x := by unit_interval
  -- ⊢ 0 ≤ ↑(Nat.choose n ν) * ↑x ^ ν * (1 - ↑x) ^ (n - ν)
  positivity
  -- 🎉 no goals
#align bernstein_nonneg bernstein_nonneg

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

@[positivity FunLike.coe _ _]
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
  ⟨(k : ℝ) / n, by
    cases' n with n
    -- ⊢ ↑↑k / ↑Nat.zero ∈ I
    · norm_num
      -- 🎉 no goals
    · have h₁ : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos _
      -- ⊢ ↑↑k / ↑(Nat.succ n) ∈ I
      have h₂ : ↑k ≤ n.succ := by exact_mod_cast Fin.le_last k
      -- ⊢ ↑↑k / ↑(Nat.succ n) ∈ I
      rw [Set.mem_Icc, le_div_iff h₁, div_le_iff h₁]
      -- ⊢ 0 * ↑(Nat.succ n) ≤ ↑↑k ∧ ↑↑k ≤ 1 * ↑(Nat.succ n)
      norm_cast
      -- ⊢ 0 * Nat.succ n ≤ ↑k ∧ ↑k ≤ 1 * Nat.succ n
      simp [h₂]⟩
      -- 🎉 no goals
#align bernstein.z bernstein.z

local postfix:90 "/ₙ" => z

theorem probability (n : ℕ) (x : I) : (∑ k : Fin (n + 1), bernstein n k x) = 1 := by
  have := bernsteinPolynomial.sum ℝ n
  -- ⊢ ∑ k : Fin (n + 1), ↑(bernstein n ↑k) x = 1
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  -- ⊢ ∑ k : Fin (n + 1), ↑(bernstein n ↑k) x = 1
  simp [AlgHom.map_sum, Finset.sum_range] at this
  -- ⊢ ∑ k : Fin (n + 1), ↑(bernstein n ↑k) x = 1
  exact this
  -- 🎉 no goals
#align bernstein.probability bernstein.probability

theorem variance {n : ℕ} (h : 0 < (n : ℝ)) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = (x : ℝ) * (1 - x) / n := by
  have h' : (n : ℝ) ≠ 0 := ne_of_gt h
  -- ⊢ ∑ k : Fin (n + 1), (↑x - ↑(k/ₙ)) ^ 2 * ↑(bernstein n ↑k) x = ↑x * (1 - ↑x) / …
  apply_fun fun x : ℝ => x * n using GroupWithZero.mul_right_injective h'
  -- ⊢ (fun x => x * ↑n) (∑ k : Fin (n + 1), (↑x - ↑(k/ₙ)) ^ 2 * ↑(bernstein n ↑k)  …
  apply_fun fun x : ℝ => x * n using GroupWithZero.mul_right_injective h'
  -- ⊢ (fun x => x * ↑n) ((fun x => x * ↑n) (∑ k : Fin (n + 1), (↑x - ↑(k/ₙ)) ^ 2 * …
  dsimp
  -- ⊢ (∑ k : Fin (n + 1), (↑x - ↑(k/ₙ)) ^ 2 * ↑(bernstein n ↑k) x) * ↑n * ↑n = ↑x  …
  conv_lhs => simp only [Finset.sum_mul, z]
  -- ⊢ ∑ x_1 : Fin (n + 1), (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n …
  conv_rhs => rw [div_mul_cancel _ h']
  -- ⊢ ∑ x_1 : Fin (n + 1), (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n …
  have := bernsteinPolynomial.variance ℝ n
  -- ⊢ ∑ x_1 : Fin (n + 1), (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n …
  apply_fun fun p => Polynomial.aeval (x : ℝ) p at this
  -- ⊢ ∑ x_1 : Fin (n + 1), (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n …
  simp [AlgHom.map_sum, Finset.sum_range, ← Polynomial.nat_cast_mul] at this
  -- ⊢ ∑ x_1 : Fin (n + 1), (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n …
  convert this using 1
  -- ⊢ ∑ x_1 : Fin (n + 1), (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n …
  · congr 1; funext k
    -- ⊢ (fun x_1 => (↑x - ↑↑x_1 / ↑n) ^ 2 * ↑(bernstein n ↑x_1) x * ↑n * ↑n) = fun x …
             -- ⊢ (↑x - ↑↑k / ↑n) ^ 2 * ↑(bernstein n ↑k) x * ↑n * ↑n = (↑n * ↑x - ↑↑k) ^ 2 *  …
    rw [mul_comm _ (n : ℝ), mul_comm _ (n : ℝ), ← mul_assoc, ← mul_assoc]
    -- ⊢ ↑n * ↑n * (↑x - ↑↑k / ↑n) ^ 2 * ↑(bernstein n ↑k) x = (↑n * ↑x - ↑↑k) ^ 2 *  …
    congr 1
    -- ⊢ ↑n * ↑n * (↑x - ↑↑k / ↑n) ^ 2 = (↑n * ↑x - ↑↑k) ^ 2
    field_simp [h]
    -- ⊢ ↑n * ↑n * (↑x * ↑n - ↑↑k) ^ 2 = (↑n * ↑x - ↑↑k) ^ 2 * ↑n ^ 2
    ring
    -- 🎉 no goals
  · ring
    -- 🎉 no goals
#align bernstein.variance bernstein.variance

end bernstein

open bernstein

local postfix:1024 "/ₙ" => z

/-- The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, f (k/n) * bernstein n k x`.
-/
def bernsteinApproximation (n : ℕ) (f : C(I, ℝ)) : C(I, ℝ) :=
  ∑ k : Fin (n + 1), f k/ₙ • bernstein n k
#align bernstein_approximation bernsteinApproximation

/-!
We now set up some of the basic machinery of the proof that the Bernstein approximations
converge uniformly.

A key player is the set `S f ε h n x`,
for some function `f : C(I, ℝ)`, `h : 0 < ε`, `n : ℕ` and `x : I`.

This is the set of points `k` in `Fin (n+1)` such that
`k/n` is within `δ` of `x`, where `δ` is the modulus of uniform continuity for `f`,
chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.

We show that if `k ∉ S`, then `1 ≤ δ^-2 * (x - k/n)^2`.
-/


namespace bernsteinApproximation

@[simp]
theorem apply (n : ℕ) (f : C(I, ℝ)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), f k/ₙ * bernstein n k x := by
  simp [bernsteinApproximation]
  -- 🎉 no goals
#align bernstein_approximation.apply bernsteinApproximation.apply

/-- The modulus of (uniform) continuity for `f`, chosen so `|f x - f y| < ε/2` when `|x - y| < δ`.
-/
def δ (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) : ℝ :=
  f.modulus (ε / 2) (half_pos h)
#align bernstein_approximation.δ bernsteinApproximation.δ

theorem δ_pos {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} : 0 < δ f ε h :=
  f.modulus_pos
#align bernstein_approximation.δ_pos bernsteinApproximation.δ_pos

/-- The set of points `k` so `k/n` is within `δ` of `x`.
-/
def S (f : C(I, ℝ)) (ε : ℝ) (h : 0 < ε) (n : ℕ) (x : I) : Finset (Fin (n + 1)) :=
  {k : Fin (n + 1) | dist k/ₙ x < δ f ε h}.toFinset
#align bernstein_approximation.S bernsteinApproximation.S

/-- If `k ∈ S`, then `f(k/n)` is close to `f x`.
-/
theorem lt_of_mem_S {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ S f ε h n x) : |f k/ₙ - f x| < ε / 2 := by
  apply f.dist_lt_of_dist_lt_modulus (ε / 2) (half_pos h)
  -- ⊢ dist k/ₙ x < ContinuousMap.modulus f (ε / 2) (_ : 0 < ε / 2)
  -- Porting note: `simp` fails to apply `Set.mem_toFinset` on its own
  simpa [S, (Set.mem_toFinset)] using m
  -- 🎉 no goals
#align bernstein_approximation.lt_of_mem_S bernsteinApproximation.lt_of_mem_S

/-- If `k ∉ S`, then as `δ ≤ |x - k/n|`, we have the inequality `1 ≤ δ^-2 * (x - k/n)^2`.
This particular formulation will be helpful later.
-/
theorem le_of_mem_S_compl {f : C(I, ℝ)} {ε : ℝ} {h : 0 < ε} {n : ℕ} {x : I} {k : Fin (n + 1)}
    (m : k ∈ (S f ε h n x)ᶜ) : (1 : ℝ) ≤ δ f ε h ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 := by
  -- Porting note: added parentheses to help `simp`
  simp only [Finset.mem_compl, not_lt, (Set.mem_toFinset), Set.mem_setOf_eq, S] at m
  -- ⊢ 1 ≤ δ f ε h ^ (-2) * (↑x - ↑k/ₙ) ^ 2
  rw [zpow_neg, ← div_eq_inv_mul, zpow_two, ← pow_two, one_le_div (pow_pos δ_pos 2), sq_le_sq,
    abs_of_pos δ_pos]
  rwa [dist_comm] at m
  -- 🎉 no goals
#align bernstein_approximation.le_of_mem_S_compl bernsteinApproximation.le_of_mem_S_compl

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
theorem bernsteinApproximation_uniform (f : C(I, ℝ)) :
    Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) := by
  simp only [Metric.nhds_basis_ball.tendsto_right_iff, Metric.mem_ball, dist_eq_norm]
  -- ⊢ ∀ (i : ℝ), 0 < i → ∀ᶠ (x : ℕ) in atTop, ‖bernsteinApproximation x f - f‖ < i
  intro ε h
  -- ⊢ ∀ᶠ (x : ℕ) in atTop, ‖bernsteinApproximation x f - f‖ < ε
  let δ := δ f ε h
  -- ⊢ ∀ᶠ (x : ℕ) in atTop, ‖bernsteinApproximation x f - f‖ < ε
  have nhds_zero := tendsto_const_div_atTop_nhds_0_nat (2 * ‖f‖ * δ ^ (-2 : ℤ))
  -- ⊢ ∀ᶠ (x : ℕ) in atTop, ‖bernsteinApproximation x f - f‖ < ε
  filter_upwards [nhds_zero.eventually (gt_mem_nhds (half_pos h)), eventually_gt_atTop 0] with n nh
    npos'
  have npos : 0 < (n : ℝ) := by positivity
  -- ⊢ ‖bernsteinApproximation n f - f‖ < ε
  have w₂ : 0 ≤ δ ^ (-2:ℤ) := zpow_neg_two_nonneg _ -- TODO: need a positivity extension for `zpow`
  -- ⊢ ‖bernsteinApproximation n f - f‖ < ε
  -- As `[0,1]` is compact, it suffices to check the inequality pointwise.
  rw [ContinuousMap.norm_lt_iff _ h]
  -- ⊢ ∀ (x : ↑I), ‖↑(bernsteinApproximation n f - f) x‖ < ε
  intro x
  -- ⊢ ‖↑(bernsteinApproximation n f - f) x‖ < ε
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  let S := S f ε h n x
  -- ⊢ ‖↑(bernsteinApproximation n f - f) x‖ < ε
  calc
    |(bernsteinApproximation n f - f) x| = |bernsteinApproximation n f x - f x| := rfl
    _ = |bernsteinApproximation n f x - f x * 1| := by rw [mul_one]
    _ = |bernsteinApproximation n f x - f x * ∑ k : Fin (n + 1), bernstein n k x| := by
      rw [bernstein.probability]
    _ = |∑ k : Fin (n + 1), (f k/ₙ - f x) * bernstein n k x| := by
      simp [bernsteinApproximation, Finset.mul_sum, sub_mul]
    _ ≤ ∑ k : Fin (n + 1), |(f k/ₙ - f x) * bernstein n k x| := (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ k : Fin (n + 1), |f k/ₙ - f x| * bernstein n k x := by
      simp_rw [abs_mul, abs_eq_self.mpr bernstein_nonneg]
    _ = (∑ k in S, |f k/ₙ - f x| * bernstein n k x) + ∑ k in Sᶜ, |f k/ₙ - f x| * bernstein n k x :=
      (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    _ < ε / 2 + ε / 2 :=
      (add_lt_add_of_le_of_lt ?_ ?_)
    _ = ε := add_halves ε
  · -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
    -- quickly give us a bound.
    calc
      ∑ k in S, |f k/ₙ - f x| * bernstein n k x ≤ ∑ k in S, ε / 2 * bernstein n k x := by
        gcongr with _ m
        exact le_of_lt (lt_of_mem_S m)
      _ = ε / 2 * ∑ k in S, bernstein n k x := by rw [Finset.mul_sum]
      -- In this step we increase the sum over `S` back to a sum over all of `Fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      _ ≤ ε / 2 * ∑ k : Fin (n + 1), bernstein n k x := by
        gcongr
        exact Finset.sum_le_univ_sum_of_nonneg fun k => bernstein_nonneg
      _ = ε / 2 := by rw [bernstein.probability, mul_one]
  · -- We now turn to working on `Sᶜ`: we control the difference term just using `‖f‖`,
    -- and then insert a `δ^(-2) * (x - k/n)^2` factor
    -- (which is at least one because we are not in `S`).
    calc
      ∑ k in Sᶜ, |f k/ₙ - f x| * bernstein n k x ≤ ∑ k in Sᶜ, 2 * ‖f‖ * bernstein n k x := by
        gcongr
        apply f.dist_le_two_norm
      _ = 2 * ‖f‖ * ∑ k in Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ 2 * ‖f‖ * ∑ k in Sᶜ, δ ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        gcongr with _ m
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        exact le_of_mem_S_compl m
      -- Again enlarging the sum from `Sᶜ` to all of `Fin (n+1)`
      _ ≤ 2 * ‖f‖ * ∑ k : Fin (n + 1), δ ^ (-2 : ℤ) * ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        gcongr
        refine Finset.sum_le_univ_sum_of_nonneg <| fun k => ?_
        positivity
      _ = 2 * ‖f‖ * δ ^ (-2 : ℤ) * ∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x := by
        conv_rhs =>
          rw [mul_assoc, Finset.mul_sum]
          simp only [← mul_assoc]
      -- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
      _ = 2 * ‖f‖ * δ ^ (-2 : ℤ) * x * (1 - x) / n := by rw [variance npos]; ring
      _ ≤ 2 * ‖f‖ * δ ^ (-2 : ℤ) * 1 * 1 / n := by gcongr <;> unit_interval
      _ < ε / 2 := by simp only [mul_one]; exact nh
#align bernstein_approximation_uniform bernsteinApproximation_uniform
