/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Kullback-Leibler divergence of finite weight functions

This file defines the Kullback-Leibler divergence `klDivFin p q` of two functions `p q : ι → ℝ`
on a `Fintype ι` as a `Finset.sum`, and proves Gibbs' inequality for it. The two functions are
not assumed to be normalized: `klDivFin` is defined for arbitrary nonnegative weights.

## Main definitions

* `klDivFin p q`: the Kullback-Leibler divergence `∑ i, p i * log (p i / q i)` of `p` from `q`.

## Main results

* `sum_sub_sum_le_klDivFin`: the bound `(∑ i, p i) - (∑ i, q i) ≤ klDivFin p q`, which requires
  no normalization hypothesis.
* `klDivFin_nonneg`: **Gibbs' inequality**, `0 ≤ klDivFin p q` when `∑ i, q i ≤ ∑ i, p i`.

## Implementation notes

`klDivFin` uses the conventions `a / 0 = 0` and `log 0 = 0`. A term with `0 = q i < p i` therefore
evaluates to `p i * log (p i / 0) = 0`, whereas the divergence has no finite value there. Each
result below thus assumes absolute continuity, `hac : ∀ i, q i = 0 → p i = 0`.

## References

* [Wikipedia, *Gibbs' inequality*](https://en.wikipedia.org/wiki/Gibbs%27_inequality)
* Cover and Thomas, *Elements of Information Theory*, Chapter 2.
-/

@[expose] public section

open Real

namespace InformationTheory

variable {ι : Type*} [Fintype ι] {p q : ι → ℝ}

/-- The Kullback-Leibler divergence `KL(p ‖ q) = ∑ i, p i * log (p i / q i)` of `p` from `q`,
measured in Nats, i.e. using natural logarithms. -/
noncomputable def klDivFin (p q : ι → ℝ) : ℝ := ∑ i, p i * log (p i / q i)

@[simp]
lemma klDivFin_self (p : ι → ℝ) : klDivFin p p = 0 := by
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rcases eq_or_ne (p i) 0 with h | h
  · simp [h]
  · simp [div_self h]

/-- `(∑ i, p i) - (∑ i, q i) ≤ klDivFin p q` for nonnegative `p` and `q` with `q i = 0 → p i = 0`.
No normalization hypothesis is required. -/
theorem sum_sub_sum_le_klDivFin (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) :
    (∑ i, p i) - (∑ i, q i) ≤ klDivFin p q := by
  have key : ∀ i, p i - q i ≤ p i * log (p i / q i) :=
    fun i ↦ sub_le_mul_log_div (hp0 i) (hq0 i) (hac i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ key i
  rwa [Finset.sum_sub_distrib] at hsum

/-- Gibbs' inequality. `0 ≤ klDivFin p q` when `∑ i, q i ≤ ∑ i, p i`. -/
theorem klDivFin_nonneg (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hac : ∀ i, q i = 0 → p i = 0) (hmass : ∑ i, q i ≤ ∑ i, p i) :
    0 ≤ klDivFin p q := by
  have h := sum_sub_sum_le_klDivFin hp0 hq0 hac
  linarith

/-- `klDivFin` is invariant under relabeling by an equivalence. -/
lemma klDivFin_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (p q : ι → ℝ) :
    klDivFin (p ∘ e) (q ∘ e) = klDivFin p q :=
  Equiv.sum_comp e fun i ↦ p i * log (p i / q i)

end InformationTheory
