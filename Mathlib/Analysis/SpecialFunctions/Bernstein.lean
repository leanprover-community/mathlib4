/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Bernstein approximations and Weierstrass' theorem

We prove that the Bernstein approximations
```
∑ k : Fin (n+1), (n.choose k * x^k * (1-x)^(n-k)) • f (k/n : ℝ)
```
for a continuous function `f : C([0,1], E)` taking values in a locally convex vector space
converge uniformly to `f` as `n` tends to infinity.
This statement directly applies to the cases when the codomain is a (semi)normed space
or, more generally, has a topology defined by a family of seminorms.

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

@[expose] public section

noncomputable section

open Filter
open scoped unitInterval Topology Uniformity

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
meta def evalBernstein : PositivityExt where eval {_ _} _zα _pα e := do
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
  simpa [Finset.sum_range]

theorem variance {n : ℕ} (hn : n ≠ 0) (x : I) :
    (∑ k : Fin (n + 1), (x - k/ₙ : ℝ) ^ 2 * bernstein n k x) = (x : ℝ) * (1 - x) / n := by
  convert congr(Polynomial.aeval (x : ℝ) $(bernsteinPolynomial.variance ℝ n) / n ^ 2) using 1
  · simp only [z, bernstein_apply, nsmul_eq_mul, bernsteinPolynomial, Finset.sum_range, map_sum,
      Polynomial.coe_aeval_eq_eval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_natCast, Polynomial.eval_X, Polynomial.eval_one]
    field_simp
    rw [← Finset.sum_div]
    field
  · simp
    field

end bernstein

open bernstein

local postfix:1024 "/ₙ" => z

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E]

/-- The `n`-th approximation of a continuous function on `[0,1]` by Bernstein polynomials,
given by `∑ k, bernstein n k x • f (k/n)`.
-/
def bernsteinApproximation (n : ℕ) (f : C(I, E)) : C(I, E) :=
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

theorem apply (n : ℕ) (f : C(I, E)) (x : I) :
    bernsteinApproximation n f x = ∑ k : Fin (n + 1), bernstein n k x • f k/ₙ := by
  simp [bernsteinApproximation]

@[simp]
theorem apply_zero (n : ℕ) (f : C(I, E)) : bernsteinApproximation n f 0 = f 0 := by
  simp [apply, Fin.sum_univ_succ, bernstein_apply, z]

@[simp]
theorem apply_one {n : ℕ} (hn : n ≠ 0) (f : C(I, E)) : bernsteinApproximation n f 1 = f 1 := by
  simp [apply, Fin.sum_univ_castSucc, bernstein_apply, hn, Nat.sub_eq_zero_iff_le]

end bernsteinApproximation

open bernsteinApproximation

/-- The Bernstein approximations
```
∑ k : Fin (n+1), f (k/n : ℝ) * n.choose k * x^k * (1-x)^(n-k)
```
for a continuous function `f : C([0,1], ℝ)` converge uniformly to `f` as `n` tends to infinity.

This is the proof given in [Richard Beals' *Analysis, an introduction*][beals-analysis], §7D,
and reproduced on wikipedia.
-/
theorem bernsteinApproximation_uniform [LocallyConvexSpace ℝ E] (f : C(I, E)) :
    Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  /- Topology on a locally convex TVS is given by a family of seminorms `‖x‖_U = gauge U x`,
  where the open symmetric convex sets `U` form a basis of neighborhoods in this topology,
  and are the open unit balls for the corresponding seminorms.
  For technical reasons, we neither assume `U`s to be open, nor symmetric. -/
  suffices ∀ U ∈ 𝓝 (0 : E), Convex ℝ U →
      ∀ᶠ n in atTop, ∀ x : I, gauge U (bernsteinApproximation n f x - f x) < 1 by
    rw [(LocallyConvexSpace.convex_basis_zero ℝ E).uniformity_of_nhds_zero_swapped
      |>.compactConvergenceUniformity_of_compact |> nhds_basis_uniformity |>.tendsto_right_iff]
    rintro U ⟨hU₀, hcU⟩
    filter_upwards [this U hU₀ hcU] with n hn x
    exact gauge_lt_one_subset_self hcU (mem_of_mem_nhds hU₀) (absorbent_nhds_zero hU₀) (hn x)
  intro U hU₀ hUc
  /- Choose a constant `C` such that `‖f x - f y‖_U ≤ C` for all `x`, `y`.
  For a normed space, this would be twice the norm of `f`. -/
  obtain ⟨C, hC⟩ : ∃ C, ∀ x y, gauge U (f x - f y) ≤ C := by
    have : Continuous fun (x, y) ↦ gauge U (f x - f y) := by fun_prop (disch := assumption)
    simpa only [BddAbove, Set.Nonempty, mem_upperBounds, Set.forall_mem_range, Prod.forall]
      using isCompact_range this |>.bddAbove
  have hC₀ : 0 ≤ C := le_trans (gauge_nonneg _) (hC 0 0)
  /- Use uniform continuity of `f` to choose `δ > 0` such that `‖f x - f y‖_U < 1 / 2`
  whenever `dist x y < δ`. -/
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0, ∀ x y : I, dist x y < δ → gauge U (f x - f y) < 1 / 2 := by
    have := CompactSpace.uniformContinuous_of_continuous (map_continuous f)
    rw [Metric.uniformity_basis_dist.uniformContinuous_iff
      (basis_sets _).uniformity_of_nhds_zero_swapped] at this
    exact this {z | gauge U z < 1 / 2} <| tendsto_gauge_nhds_zero hU₀
      |>.eventually_lt_const <| by positivity
  -- Take `n ≠ 0` such that `C / δ ^ 2 / n < 1 / 2`.
  have nhds_zero := tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2)
  filter_upwards [nhds_zero.eventually_lt_const (half_pos one_pos), eventually_ne_atTop 0]
    with n nh hn₀ x
  -- The idea is to split up the sum over `k` into two sets,
  -- `S`, where `x - k/n < δ`, and its complement.
  set S : Finset (Fin (n + 1)) := {k : Fin (n + 1) | dist k/ₙ x < δ}
  calc
    gauge U (bernsteinApproximation n f x - f x)
      = gauge U (∑ k : Fin (n + 1), bernstein n k x • (f k/ₙ - f x)) := by
      simp [bernsteinApproximation.apply, smul_sub, ← Finset.sum_smul]
    _ ≤ ∑ k : Fin (n + 1), gauge U (bernstein n k x • (f k/ₙ - f x)) :=
      gauge_sum_le hUc (absorbent_nhds_zero hU₀) _ _
    _ = ∑ k : Fin (n + 1), bernstein n k x * gauge U (f k/ₙ - f x) := by
      simp only [gauge_smul_of_nonneg, bernstein_nonneg, smul_eq_mul]
    _ = (∑ k ∈ S, bernstein n k x * gauge U (f k/ₙ - f x)) +
          ∑ k ∈ Sᶜ, bernstein n k x * gauge U (f k/ₙ - f x) :=
      (S.sum_add_sum_compl _).symm
    -- We'll now deal with the terms in `S` and the terms in `Sᶜ` in separate calc blocks.
    _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt ?_ ?_
    _ = 1 := add_halves 1
  · -- We now work on the terms in `S`: uniform continuity and `bernstein.probability`
    -- quickly give us a bound.
    calc
      ∑ k ∈ S, bernstein n k x * gauge U (f k/ₙ - f x) ≤ ∑ k ∈ S, bernstein n k x * (1 / 2) := by
        gcongr with k hk
        refine (hδ _ _ ?_).le
        simpa [S] using hk
      _ = 1 / 2 * ∑ k ∈ S, bernstein n k x := by rw [mul_comm, Finset.sum_mul]
      -- In this step we increase the sum over `S` back to a sum over all of `Fin (n+1)`,
      -- so that we can use `bernstein.probability`.
      _ ≤ 1 / 2 * ∑ k : Fin (n + 1), bernstein n k x := by gcongr; exact S.subset_univ
      _ = 1 / 2 := by rw [bernstein.probability, mul_one]
  · -- We now turn to working on `Sᶜ`: we control the difference term just using `C`,
    -- and then insert a `(x - k/n)^2 / δ^2` factor
    -- (which is at least one because we are not in `S`).
    calc
      ∑ k ∈ Sᶜ, bernstein n k x * gauge U (f k/ₙ - f x) ≤ ∑ k ∈ Sᶜ, C * bernstein n k x := by
        simp only [mul_comm (bernstein n _ x)]
        gcongr
        apply hC
      _ = C * ∑ k ∈ Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ C * ∑ k ∈ Sᶜ, ((x : ℝ) - k/ₙ) ^ 2 / δ ^ 2 * bernstein n k x := by
        gcongr with k hk
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        simpa [one_le_div₀, hδ₀, sq_le_sq, S, abs_of_pos, ← Real.dist_eq, dist_comm (x : ℝ)]
          using hk
      -- Again enlarging the sum from `Sᶜ` to all of `Fin (n+1)`
      _ ≤ C * ∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 / δ ^ 2 * bernstein n k x := by
        gcongr; exact Sᶜ.subset_univ
      _ = C * (∑ k : Fin (n + 1), ((x : ℝ) - k/ₙ) ^ 2 * bernstein n k x) / δ ^ 2 := by
        simp only [← mul_div_right_comm, ← mul_div_assoc, ← Finset.sum_div]
      -- `bernstein.variance` and `x ∈ [0,1]` gives the uniform bound
      _ = C / δ ^ 2 * x * (1 - x) / n := by rw [variance hn₀]; ring
      _ ≤ C / δ ^ 2 * 1 * 1 / n := by gcongr <;> unit_interval
      _ < 1 / 2 := by simpa only [mul_one]
