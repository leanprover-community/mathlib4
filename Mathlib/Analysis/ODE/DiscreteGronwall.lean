/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Discrete Grönwall inequality

Various forms of the discrete Grönwall inequality, bounding solutions to recurrence
inequalities `u (n+1) ≤ c n * u n + b n` and `u (n+1) ≤ (1 + c n) * u n + b n`.

## Main results

* `discrete_gronwall_prod_general`: product form, over any linearly ordered commutative ring.
* `discrete_gronwall`: classical exponential bound for the `(1 + c)` form, over `ℝ`.
* `discrete_gronwall_Ico`: uniform bound over an interval, over `ℝ`.

## References

* [T. H. Grönwall, *Note on the derivatives with respect to a parameter of the solutions of a
  system of differential equations*][Gronwall_1919]

## See also

* `Mathlib.Analysis.ODE.Gronwall` for the continuous Grönwall inequality for ODEs.
-/

@[expose] public section

open Real Finset

section General

/-! ### Generalized product form -/

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {u b c : ℕ → R}

/-- Discrete Grönwall inequality, product form: if `u (n+1) ≤ c n * u n + b n` and `1 ≤ c n`
then `u n ≤ u n₀ * ∏ c i + ∑ b k * ∏ c i` over the appropriate ranges. -/
theorem discrete_gronwall_prod_general {n₀ : ℕ} (hu : ∀ n ≥ n₀, u (n + 1) ≤ c n * u n + b n)
    (hc : ∀ n ≥ n₀, 1 ≤ c n) ⦃n : ℕ⦄ (hn : n₀ ≤ n) :
    u n ≤ u n₀ * ∏ i ∈ Ico n₀ n, c i +
      ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, c i := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hck : 0 ≤ c k := zero_le_one.trans (hc k hk)
    have heq : c k * ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i + b k =
        ∑ j ∈ Ico n₀ (k + 1), b j * ∏ i ∈ Ico (j + 1) (k + 1), c i := by
      rw [sum_Ico_succ_top hk, mul_sum, Ico_self, prod_empty, mul_one]
      refine congr_arg (· + b k) (sum_congr rfl fun j hj ↦ ?_)
      rw [prod_Ico_succ_top (by have := mem_Ico.mp hj; omega)]; ring
    calc u (k + 1)
      _ ≤ c k * u k + b k := hu k hk
      _ ≤ c k * (u n₀ * ∏ i ∈ Ico n₀ k, c i +
            ∑ j ∈ Ico n₀ k, b j * ∏ i ∈ Ico (j + 1) k, c i) + b k := by gcongr
      _ = u n₀ * ∏ i ∈ Ico n₀ (k + 1), c i +
            ∑ j ∈ Ico n₀ (k + 1), b j * ∏ i ∈ Ico (j + 1) (k + 1), c i := by
          rw [← heq, ← prod_Ico_mul_eq_prod_Ico_add_one hk]; ring

end General

/-! ### Real-valued exponential form -/

variable {u b c : ℕ → ℝ}

/-- Discrete Grönwall inequality, exponential form: if `u (n+1) ≤ (1 + c n) * u n + b n` with
`b`, `c`, and `u n₀` non-negative, then `u n ≤ (u n₀ + ∑ b k) * exp (∑ c i)`. -/
theorem discrete_gronwall {n₀ : ℕ} (hun₀ : 0 ≤ u n₀)
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n) (hc : ∀ n ≥ n₀, 0 ≤ c n)
    (hb : ∀ n ≥ n₀, 0 ≤ b n) ⦃n : ℕ⦄ (hn : n₀ ≤ n) :
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) := by
  have hprod_le_exp : ∏ i ∈ Ico n₀ n, (1 + c i) ≤ exp (∑ i ∈ Ico n₀ n, c i) := by
    rw [exp_sum]
    exact Finset.prod_le_prod (fun i hi ↦ by linarith [hc i (mem_Ico.mp hi).1])
      (fun i _ ↦ by linarith [add_one_le_exp (c i)])
  calc u n
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
          ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico (k + 1) n, (1 + c i) :=
        discrete_gronwall_prod_general hu (by grind) hn
    _ ≤ u n₀ * ∏ i ∈ Ico n₀ n, (1 + c i) +
          ∑ k ∈ Ico n₀ n, b k * ∏ i ∈ Ico n₀ n, (1 + c i) :=
        add_le_add le_rfl <| sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
          (prod_le_prod_of_subset_of_one_le
            (Ico_subset_Ico_left (by have := mem_Ico.mp hj; omega))
            (fun i hi ↦ by
              have := mem_Ico.mp hj; have := mem_Ico.mp hi; linarith [hc i (by omega)])
            (fun i hi _ ↦ by linarith [hc i (mem_Ico.mp hi).1]))
          (hb j (mem_Ico.mp hj).1)
    _ = (u n₀ + ∑ k ∈ Ico n₀ n, b k) * ∏ i ∈ Ico n₀ n, (1 + c i) := by rw [add_mul, sum_mul]
    _ ≤ (u n₀ + ∑ k ∈ Ico n₀ n, b k) * exp (∑ i ∈ Ico n₀ n, c i) :=
        mul_le_mul_of_nonneg_left hprod_le_exp (add_nonneg hun₀ (sum_nonneg <| by grind))

/-- Discrete Grönwall inequality, uniform bound: a single bound holding for all `n ∈ [n₀, n₁)`. -/
theorem discrete_gronwall_Ico {n₀ n₁ : ℕ} (hun₀ : 0 ≤ u n₀)
    (hu : ∀ n ≥ n₀, u (n + 1) ≤ (1 + c n) * u n + b n)
    (hc : ∀ n ≥ n₀, 0 ≤ c n) (hb : ∀ n ≥ n₀, 0 ≤ b n) ⦃n : ℕ⦄ (hn : n ∈ Ico n₀ n₁) :
    u n ≤ (u n₀ + ∑ k ∈ Ico n₀ n₁, b k) * exp (∑ i ∈ Ico n₀ n₁, c i) := by
  have : 0 ≤ ∑ k ∈ Ico n₀ n₁, b k := sum_nonneg <| by grind
  exact (discrete_gronwall hun₀ hu hc hb (mem_Ico.mp hn).1).trans (by gcongr <;> grind)
