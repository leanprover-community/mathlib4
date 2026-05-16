/-
Copyright (c) 2026 Jacob Cascone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Cascone
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Robin's Inequality and the Riemann Hypothesis

Robin (1984) proved that the Riemann Hypothesis is equivalent to the inequality
$$\sigma_1(n) < e^{\gamma} \cdot n \cdot \ln(\ln(n))$$
holding for all $n > 5040$, where $\sigma_1(n)$ is the sum of divisors of $n$
and $\gamma$ is the Euler-Mascheroni constant.

Lagarias (2002) proved an equivalent reformulation:
$$\sigma_1(n) \leq H_n + \exp(H_n) \cdot \ln(H_n)$$
for all $n \geq 1$, where $H_n$ is the $n$-th harmonic number.

## Main definitions

* `robinBound`: the function $n \mapsto e^\gamma \cdot n \cdot \ln(\ln(n))$.
* `lagariasBound`: the function $n \mapsto H_n + e^{H_n} \cdot \ln(H_n)$.

## Main results

* `robin_iff_RH`: Robin's inequality is equivalent to the Riemann Hypothesis.
* `lagarias_iff_RH`: Lagarias' inequality is equivalent to the Riemann Hypothesis.

## References

* [G. Robin, *Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*,
  J. Math. Pures Appl. 63 (1984), 187-213]
* [J. Lagarias, *An elementary problem equivalent to the Riemann hypothesis*,
  Amer. Math. Monthly 109 (2002), 534-543]

## TODO

The proofs of `robin_iff_RH` and `lagarias_iff_RH` are left as `sorry`.
The Robin direction (RH → inequality) requires deep analytic number theory
following Robin (1984). The converse uses Gronwall's theorem on superior
highly composite numbers. Completing these proofs is a major Mathlib project.
-/

open ArithmeticFunction

/-- The Robin bound: `e^γ · n · ln(ln(n))`. -/
noncomputable def robinBound (n : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))

/-- The Lagarias bound: `H_n + exp(H_n) · ln(H_n)`. -/
noncomputable def lagariasBound (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- Robin's inequality: for `n > 5040`, `σ₁(n) < e^γ · n · ln(ln(n))`.
This follows from the Riemann Hypothesis (Robin 1984). -/
theorem robin_inequality_of_RH (hRH : RiemannHypothesis) :
    ∀ n : ℕ, n > 5040 → (sigma 1 n : ℝ) < robinBound n := by
  sorry

/-- The converse: if Robin's inequality holds for all `n > 5040`, then the
Riemann Hypothesis is true (Robin 1984). -/
theorem RH_of_robin_inequality
    (h : ∀ n : ℕ, n > 5040 → (sigma 1 n : ℝ) < robinBound n) :
    RiemannHypothesis := by
  sorry

/-- **Robin's theorem** (Robin 1984): The Riemann Hypothesis is equivalent to Robin's inequality
`σ₁(n) < e^γ · n · ln(ln(n))` holding for all `n > 5040`. -/
theorem robin_iff_RH :
    RiemannHypothesis ↔
      ∀ n : ℕ, n > 5040 → (sigma 1 n : ℝ) < robinBound n :=
  ⟨robin_inequality_of_RH, RH_of_robin_inequality⟩

/-- Lagarias' inequality: for `n ≥ 1`, `σ₁(n) ≤ H_n + exp(H_n) · ln(H_n)`.
This follows from the Riemann Hypothesis (Lagarias 2002). -/
theorem lagarias_inequality_of_RH (hRH : RiemannHypothesis) :
    ∀ n : ℕ, n ≥ 1 → (sigma 1 n : ℝ) ≤ lagariasBound n := by
  sorry

/-- The converse: Lagarias' inequality implies the Riemann Hypothesis (Lagarias 2002). -/
theorem RH_of_lagarias_inequality
    (h : ∀ n : ℕ, n ≥ 1 → (sigma 1 n : ℝ) ≤ lagariasBound n) :
    RiemannHypothesis := by
  sorry

/-- **Lagarias' theorem** (Lagarias 2002): The Riemann Hypothesis is equivalent to
`σ₁(n) ≤ H_n + exp(H_n) · ln(H_n)` for all `n ≥ 1`. -/
theorem lagarias_iff_RH :
    RiemannHypothesis ↔
      ∀ n : ℕ, n ≥ 1 → (sigma 1 n : ℝ) ≤ lagariasBound n :=
  ⟨lagarias_inequality_of_RH, RH_of_lagarias_inequality⟩
