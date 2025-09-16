/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.GCongr

/-!
# The Schwartz-Zippel lemma

This file contains a proof of the
[Schwartz-Zippel](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma) lemma.

This lemma tells us that the probability that a nonzero multivariable polynomial over an integral
domain evaluates to zero at a random point is bounded by the degree of the polynomial over the size
of the field, or more generally, that a nonzero multivariable polynomial over any integral domain
has a low probability of being zero when evaluated at points drawn at random from some finite subset
of the field. This lemma is useful as a probabilistic polynomial identity test.

## Main results

- `MvPolynomial.schwartz_zippel_sup_sum`:
  Sharper version of Schwartz-Zippel for a dependent product of sets `S i`, with the RHS being
  the supremum of `∑ i, degᵢ s / #(S i)` ranging over monomials `s` of the polynomial.
- `MvPolynomial.schwartz_zippel_sum_degreeOf`:
  Schwartz-Zippel for a dependent product of sets `S i`,
  with the RHS being the sum of `degᵢ p / #(S i)`.
- `MvPolynomial.schwartz_zippel_totalDegree`:
  Nondependent version of `schwartz_zippel_sup_sum`, with the RHS being `p.totalDegree / #S`.

## TODO

* Generalize to polynomials over arbitrary variable types
* Prove the stronger statement that one can replace the degrees of `p` in the RHS by the degrees of
  the maximal monomial of `p` in some lexicographic order.
* Write a tactic to apply this lemma to a given polynomial

## References

* [demillo_lipton_1978]
* [schwartz_1980]
* [zippel_1979]
-/

open Fin Finset Fintype

local notation:70 s:70 " ^^ " n:71 => piFinset fun i : Fin n ↦ s i

namespace MvPolynomial
variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

-- A user should be able to provide `hp` as a named argument
-- regardless of whether one has used pattern-matching or induction to prove the lemma.
set_option linter.unusedVariables false in
/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from a product of finite subsets `S i` of the integral
domain is bounded by the supremum of `∑ i, degᵢ s / #(S i)` ranging over monomials `s` of `p`. -/
lemma schwartz_zippel_sup_sum :
    ∀ {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Fin n → Finset R),
      #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤
        p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0)
  | 0, p, hp, S => by
    -- Because `p` is a polynomial over zero variables, it is constant.
    rw [p.eq_C_of_isEmpty] at *
    simp [C_ne_zero.mp hp]
    -- Now, assume that the theorem holds for all polynomials in `n` variables.
  | n + 1, p, hp, S => by
    -- We can consider `p` to be a polynomial over multivariable polynomials in one fewer variables.
    set p' : Polynomial (MvPolynomial (Fin n) R) := finSuccEquiv R n p with hp'
    -- Since `p` is not identically zero, there is some `k` such that `pₖ` is not identically zero.
    -- WLOG `k` is the largest such.
    set k := p'.natDegree with hk
    set pₖ := p'.leadingCoeff with hpₖ
    have hp'₀ : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hp
    have hpₖ₀ : pₖ ≠ 0 := by simpa [pₖ, k]
    calc
      -- We split the set of possible zeros into a union of two cases.
      #{x ∈ S ^^ (n + 1) | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0)
          -- In the first case, `pₖ` evaluates to `0`.
        = #{x ∈ S ^^ (n + 1) | eval x p = 0 ∧ eval (tail x) pₖ = 0} / ∏ i, (#(S i) : ℚ≥0)
          -- In the second case, `pₖ` does not evaluate to `0`.
          + #{x ∈ S ^^ (n + 1) | eval x p = 0 ∧ eval (tail x) pₖ ≠ 0} / ∏ i, (#(S i) : ℚ≥0) := by
        rw [← add_div, ← Nat.cast_add, ← card_union_add_card_inter, filter_union_right,
          ← filter_and]
        simp [← and_or_left, em, and_and_and_comm]
      _ ≤ (pₖ.support.sup fun s ↦ ∑ i, (s i / #(S i.succ) : ℚ≥0)) + p.degreeOf 0 / #(S 0) := ?_
      _ ≤ p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0) := ?_
    · gcongr ?_ + ?_
      · -- We bound the size of the first set by induction
        calc
          #{x ∈ S ^^ (n + 1) | eval x p = 0 ∧ eval (tail x) pₖ = 0} / ∏ i, (#(S i) : ℚ≥0)
            ≤ #{x ∈ S ^^ (n + 1) | eval (tail x) pₖ = 0} / ∏ i, (#(S i) : ℚ≥0) := by
            gcongr; exact fun x hx ↦ hx.2
          _ = #(S 0) * #{xₜ ∈ tail S ^^ n | eval xₜ pₖ = 0}
              / (#(S 0) * (∏ i, #(S (.succ i)) : ℚ≥0)) := by
            rw [card_consEquiv_filter_piFinset S fun x ↦ eval x pₖ = 0, prod_univ_succ, tail_def]
            norm_cast
          _ ≤ #{xₜ ∈ tail S ^^ n | eval xₜ pₖ = 0} / ∏ i, (#(S (.succ i)) : ℚ≥0) :=
            mul_div_mul_left_le (by positivity)
          _ ≤ (pₖ.support.sup fun s ↦ ∑ i, (s i / #(S (.succ i)) : ℚ≥0)) :=
            schwartz_zippel_sup_sum hpₖ₀ _
      · -- We bound the second set by noting that if `x` is in it, then `x₀` is the root of
        -- the univariate polynomial`pₓ` obtained by evaluating each (multivariate polynomial)
        -- coefficient at `xₜ`. Since `pₓ` has degree `k`, there are at most `k` such `x₀` for
        -- each `xₜ`, which gives the result.
        calc
          #{x ∈ S ^^ (n + 1) | eval x p = 0 ∧ eval (tail x) pₖ ≠ 0} / ∏ i, (#(S i) : ℚ≥0)
            ≤ ↑(p.degreeOf 0 * ∏ i, #(S (.succ i))) / ∏ i, (#(S i) : ℚ≥0) := ?_
          _ = p.degreeOf 0 * (∏ i, #(S (.succ i))) / (#(S 0) * ∏ i, #(S (.succ i))) := by
            norm_cast; rw [prod_univ_succ]
          _ ≤ (p.degreeOf 0 / #(S 0) : ℚ≥0) := mul_div_mul_right_le (by positivity)
        gcongr
        calc
          #{x ∈ S ^^ (n + 1) | eval x p = 0 ∧ eval (tail x) pₖ ≠ 0}
            = #{x ∈ S ^^ (n + 1) | eval (tail x) pₖ ≠ 0 ∧ eval x p = 0} := by simp_rw [and_comm]
          _ = #({xₜ ∈ tail S ^^ n | eval xₜ pₖ ≠ 0}.biUnion fun xₜ ↦ image (fun x₀ ↦ (x₀, xₜ))
                {x₀ ∈ S 0 | eval (cons x₀ xₜ) p = 0}) := by
            rw [← filter_filter, filter_piFinset_eq_map_consEquiv S (fun r ↦ eval r pₖ ≠ 0),
              filter_map, card_map, product_eq_biUnion_right, filter_biUnion]
            simp [Function.comp_def, filter_image]
            rfl
          _ ≤ ∑ xₜ ∈ tail S ^^ n with eval xₜ pₖ ≠ 0,
                #(image (fun x₀ ↦ (x₀, xₜ)) {x₀ ∈ S 0 | eval (cons x₀ xₜ) p = 0}) :=
            card_biUnion_le
          _ ≤ ∑ xₜ ∈ tail S ^^ n with eval xₜ pₖ ≠ 0, #{x₀ ∈ S 0 | eval (cons x₀ xₜ) p = 0} := by
            gcongr; exact card_image_le
          _ ≤ ∑ xₜ ∈ tail S ^^ n with eval xₜ pₖ ≠ 0, p.degreeOf 0 := ?_
          _ ≤ ∑ _xₜ ∈ tail S ^^ n, p.degreeOf 0 := by gcongr; exact filter_subset ..
          _ = p.degreeOf 0 * ∏ i, #(S (.succ i)) := by simp [mul_comm, tail]
        gcongr with xₜ hxₜ
        set pₓ := p'.map (eval xₜ) with hpₓ
        have hpₓdeg : pₓ.natDegree = k := by
          rw [hpₓ, hk, Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ (mem_filter.1 hxₜ).2]
        have hpₓ₀ : pₓ ≠ 0 := fun h ↦ (mem_filter.1 hxₜ).2 <| by
          rw [hpₖ, Polynomial.leadingCoeff, ← hk, ← hpₓdeg, h, Polynomial.natDegree_zero,
            ← Polynomial.coeff_map, ← hpₓ, h, Polynomial.coeff_zero]
        calc
          #{x₀ ∈ S 0 | eval (cons x₀ xₜ) p = 0} ≤ #pₓ.roots.toFinset := by
            gcongr
            simp +contextual [subset_iff, eval_eq_eval_mv_eval', pₓ, hpₓ₀, p']
          _ ≤ Multiset.card pₓ.roots := pₓ.roots.toFinset_card_le
          _ ≤ pₓ.natDegree := pₓ.card_roots'
          _ = k := hpₓdeg
          _ ≤ p.degreeOf 0 := by
            have :
              (ofLex (AddMonoidAlgebra.supDegree toLex p'.leadingCoeff)).cons k ∈ p.support := by
              rwa [← support_coeff_finSuccEquiv, mem_support_iff, ← hp', hk,
                ← Polynomial.leadingCoeff, ← hpₖ, ← leadingCoeff_toLex,
                AddMonoidAlgebra.leadingCoeff_ne_zero toLex.injective]
            simpa using monomial_le_degreeOf 0 this
    · rw [Finset.sup_add (support_nonempty.mpr hpₖ₀)]
      apply Finset.sup_le
      rintro i hi
      refine le_sup_of_le (mem_support_coeff_finSuccEquiv.mp hi) ?_
      rw [Fin.sum_univ_succ, add_comm]
      dsimp
      gcongr
      simp [natDegree_finSuccEquiv, p']

/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from a product of finite subsets `S i` of the integral
domain is bounded by the sum of `degᵢ p / #(S i)`. -/
lemma schwartz_zippel_sum_degreeOf {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (S : Fin n → Finset R) :
    #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0) := by
  calc
    _ ≤ p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0) := schwartz_zippel_sup_sum hp S
    _ ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0) := Finset.sup_le fun s hs ↦ by
      gcongr with i; exact monomial_le_degreeOf i hs

/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from some finite subset `S` of the integral domain is
bounded by the degree of `p` over `#S`. This version presents this lemma in terms of `Finset`. -/
lemma schwartz_zippel_totalDegree {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Finset R) :
    #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (#S ^ n : ℚ≥0) ≤ p.totalDegree / #S :=
  calc
    _ = #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (∏ i : Fin n, #S : ℚ≥0) := by simp
    _ ≤ p.support.sup fun s ↦ ∑ i, (s i / #S : ℚ≥0) := schwartz_zippel_sup_sum hp _
    _ = p.totalDegree / #S := by
      obtain rfl | hs := S.eq_empty_or_nonempty
      · simp
        simp only [← _root_.bot_eq_zero, sup_bot]
      simp_rw [totalDegree, Nat.cast_finsetSup]
      rw [sup_div₀ (ha := show 0 < (#S : ℚ≥0) by positivity)]
      simp [← sum_div, Finsupp.sum_fintype]

end MvPolynomial
