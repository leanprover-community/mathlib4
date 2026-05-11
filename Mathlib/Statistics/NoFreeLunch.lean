/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# No-free-lunch adversary core (Devroye–Györfi–Lugosi)

This module formalizes the **finite-class algebraic core** of the
Devroye–Györfi–Lugosi (DGL) adversary argument, following the
presentation in Devroye, Györfi, Lugosi (1996),
*A Probabilistic Theory of Pattern Recognition*, Section 7.2, and the
binary specialization of Shalev-Shwartz, Ben-David (2014),
*Understanding Machine Learning*, Theorem 5.1.

The DGL adversary argument shows that for any deterministic learning
rule `A : (X × Y)^n → (X → Y)`, there exists a distribution `D` on
`X × Y` such that the excess risk of `A` over the Bayes optimum is at
least a positive absolute constant. The proof proceeds by introducing
a finite hard hypothesis class `(f_θ)_{θ ∈ Θ}` and taking the uniform
prior over `Θ`; the algorithm's worst-case risk is then lower bounded
by its average risk over the prior, and pigeonhole produces the bad
`θ`.

The contents of this file are the purely algebraic ingredients of that
argument, isolated from the learning-theoretic semantics. The full
measure-theoretic DGL adversary is left to a future PR (see "Future
work" below).

## Main definitions

This file contains no new definitions; it is a collection of bounded
algebraic lemmas about finite families of real numbers and a single
existence statement for the uniform prior.

## Main results

* `Statistics.NoFreeLunch.exists_uniform_pmf` —
  the uniform prior `i ↦ 1 / K` is a probability mass function on
  `Fin K`.
* `Statistics.NoFreeLunch.average_le_sup'` —
  `(∑ i, R i) / K ≤ Finset.univ.sup' _ R` (max dominates the average).
* `Statistics.NoFreeLunch.exists_index_average_le` —
  pigeonhole on a real risk vector: some index `i` has
  `R i ≥ (∑ j, R j) / K`.
* `Statistics.NoFreeLunch.exists_index_average_le_of_bounded` —
  same conclusion under the standard `0 ≤ R i ≤ 1` regime used by the
  DGL no-free-lunch argument.
* `Statistics.NoFreeLunch.average_le_max_two` —
  the `K = 2` specialization `(R₀ + R₁) / 2 ≤ max R₀ R₁`, which is the
  form used in the binary no-free-lunch proof.

## Implementation notes

The lemmas are stated for `R : Fin K → ℝ` rather than for an arbitrary
finset so that the resulting averages are literal divisions by the
natural number `K`. This is the form in which the DGL argument is
usually applied (the index set parameterizes leaves of a hard
hypothesis tree, typically of size a power of two).

The maximum is expressed using `Finset.sup'` over `Finset.univ`, which
is the standard way to take a maximum of a nonempty family in Mathlib.

## References

* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern
  Recognition*, Springer, 1996, Section 7.2 (no-free-lunch adversary).
* S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning:
  From Theory to Algorithms*, Cambridge University Press, 2014,
  Section 5.1 / Theorem 5.1 (binary no-free-lunch).

## Tags

no-free-lunch, adversary, learning theory, minimax, pigeonhole
-/

namespace Statistics.NoFreeLunch

open Finset

@[expose] public section

variable {K : ℕ}

/-- **Uniform prior on `Fin K`.** For any positive `K : ℕ`, the constant
function `i ↦ 1 / K` is a probability mass function on `Fin K`: it is
nonnegative, sums to `1`, and equals `1 / K` at every point.

This is the prior used in the DGL adversary construction: against a
deterministic learning rule we draw the target hypothesis from a
uniform distribution over a finite hard class, so the algorithm's
worst-case risk dominates its uniform-prior average risk. -/
theorem exists_uniform_pmf (hK : 0 < K) :
    ∃ p : Fin K → ℝ,
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧ ∀ i, p i = 1 / (K : ℝ) := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  refine ⟨fun _ => (1 : ℝ) / (K : ℝ), ?_, ?_, ?_⟩
  · intro _
    positivity
  · have hsum : (∑ _i : Fin K, (1 : ℝ) / (K : ℝ)) = (K : ℝ) * (1 / (K : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum, mul_one_div, div_self hKne]
  · intro _; rfl

/-- **Average is bounded by the maximum.** For any nonempty family of
real numbers `R : Fin K → ℝ`, the average `(∑ i, R i) / K` is at most
the maximum value `Finset.univ.sup' _ R`.

This is one half of the DGL "worst case dominates the average":
combined with `Finset.exists_mem_eq_sup'` it yields an index whose risk
is at least the average. -/
theorem average_le_sup' (R : Fin K → ℝ) (hK : 0 < K) :
    (∑ i, R i) / (K : ℝ) ≤
      (Finset.univ : Finset (Fin K)).sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩) R := by
  classical
  set hne : (Finset.univ : Finset (Fin K)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩
  set M : ℝ := (Finset.univ : Finset (Fin K)).sup' hne R with hM
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin K)), R i ≤ M := by
    intro i hi
    exact Finset.le_sup' (f := R) hi
  have hsum : (∑ i, R i) ≤ (∑ _i : Fin K, M) :=
    Finset.sum_le_sum hle
  have hcard : (∑ _i : Fin K, M) = (K : ℝ) * M := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum' : (∑ i, R i) ≤ (K : ℝ) * M := by
    rw [hcard] at hsum; exact hsum
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  exact (div_le_iff₀ hKpos).mpr (by linarith [hsum'])

/-- **Pigeonhole on a real risk vector.** Given a nonempty family of
real numbers `R : Fin K → ℝ`, some index `i` satisfies
`R i ≥ (∑ j, R j) / K`.

Operationally, the index attaining the maximum works. Combined with
`average_le_sup'` this is the DGL adversary step: against any
algorithm, *some* target hypothesis achieves at least the prior-average
risk. -/
theorem exists_index_average_le (R : Fin K → ℝ) (hK : 0 < K) :
    ∃ i, (∑ j, R j) / (K : ℝ) ≤ R i := by
  classical
  set hne : (Finset.univ : Finset (Fin K)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hK⟩⟩
  obtain ⟨i, _hi, hieq⟩ :=
    Finset.exists_mem_eq_sup' (f := R) hne
  refine ⟨i, ?_⟩
  have hmax := average_le_sup' (R := R) hK
  rw [hieq] at hmax
  exact hmax

/-- **Finite-class DGL adversary, bounded-risk form.** Specialization of
`exists_index_average_le` to the standard regime in which risks are
nonnegative and bounded above by `1`. The boundedness assumptions are
not strictly necessary for the algebraic conclusion, but they match the
hypotheses used by the DGL adversary argument (where `R i` is the `0-1`
risk of an algorithm trained on `n` samples).

Concretely: against any deterministic algorithm and any finite hard
class of size `K`, there exists a hypothesis `i` whose risk is at least
the uniform-prior average risk. -/
theorem exists_index_average_le_of_bounded (R : Fin K → ℝ)
    (hK : 0 < K) (_hRnn : ∀ i, 0 ≤ R i) (_hRle : ∀ i, R i ≤ 1) :
    ∃ i, (∑ j, R j) / (K : ℝ) ≤ R i :=
  exists_index_average_le R hK

/-- **Two-class DGL specialization.** The maximum of two real numbers
dominates their average: `(R₀ + R₁) / 2 ≤ max R₀ R₁`.

This is the form of the DGL inequality used in the binary
no-free-lunch proof (where `R₀` and `R₁` are the risks attained on the
two hypotheses of a hard pair). It is the case `K = 2` of
`average_le_sup'`, but stated directly using `max` to keep it
elementary. -/
theorem average_le_max_two (R₀ R₁ : ℝ) : (R₀ + R₁) / 2 ≤ max R₀ R₁ := by
  rcases le_total R₀ R₁ with h | h
  · -- `max = R₁`; reduce to `R₀ ≤ R₁`.
    have : (R₀ + R₁) / 2 ≤ R₁ := by linarith
    simpa [max_eq_right h] using this
  · -- `max = R₀`; reduce to `R₁ ≤ R₀`.
    have : (R₀ + R₁) / 2 ≤ R₀ := by linarith
    simpa [max_eq_left h] using this

/-! ### Examples / sanity checks -/

/-- For two equal risks, the max equals their average (and equals the
common value). This is the boundary case of `average_le_max_two`. -/
example (R : ℝ) : max R R = (R + R) / 2 := by
  have h₁ : max R R = R := max_self R
  have h₂ : (R + R) / 2 = R := by ring
  rw [h₁, h₂]

/-- The `K = 2` specialization of `exists_index_average_le` reproduces
the basic no-free-lunch form: in any pair of risks, at least one is at
least the average. -/
example (R₀ R₁ : ℝ) :
    ∃ i : Fin 2, (R₀ + R₁) / 2 ≤ ![R₀, R₁] i := by
  have h := exists_index_average_le (K := 2)
    (R := ![R₀, R₁]) (by decide)
  -- Rewrite the sum `∑ j, ![R₀,R₁] j = R₀ + R₁` and the denominator.
  have hsum : (∑ j : Fin 2, ![R₀, R₁] j) = R₀ + R₁ := by
    simp [Fin.sum_univ_two]
  simpa [hsum, show ((2 : ℕ) : ℝ) = 2 from by norm_cast] using h

end

end Statistics.NoFreeLunch
