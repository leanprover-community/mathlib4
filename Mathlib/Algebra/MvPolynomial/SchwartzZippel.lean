/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Yaël Dillies
-/
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Tuple.Finset

/-!
# The Schwartz-Zippel lemma

This file contains a proof of the
[Schwartz-Zippel](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma) lemma.

This lemma tells us that the probability that a nonzero multivariable polynomial over an integral
domain evaluates to zero at a random point is bounded by the degree of the polynomial over the size
of the field, or more generally, that a nonzero multivariable polynomial over any integral domain
has a low probability of being zero when evaluated at points drawn at random from some finite subset
of the field. This lemma is useful as a probabilistic polynomial identity test.

## TODO

* Generalize to polynomials over arbitrary variable types
* Write a tactic to apply this lemma to a given polynomial

## References

* [demillo_lipton_1978]
* [schwartz_1980]
* [zippel_1979]
-/

local prefix:100 "#" => Finset.card
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun i : Fin n ↦ s i

open Fin Finset Fintype

namespace MvPolynomial
variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

-- We want to be able to refer to `hp` and `hm`.
set_option linter.unusedVariables false in
/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from some finite subset `S` of the integral domain is
bounded by the degree of `p` over `|S|`. This version presents this lemma in terms of `Finset`. -/
lemma schwartz_zippel : ∀ {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Fin n → Finset R),
    #{f ∈ S ^^ n | eval f p = 0} / ∏ i, (#S i : ℚ≥0) ≤ ∑ i, (p.degreeOf i / #S i : ℚ≥0)
  | 0, p, hp, S => by
    -- Because `p` is a polynomial over zero variables, it is constant.
    rw [p.eq_C_of_isEmpty] at *
    simpa using hp
    -- Now, assume that the theorem holds for all polynomials in `n` variables.
  | n + 1, p, hp, S => by
    -- We can consider `p` to be a polynomial over multivariable polynomials in one fewer variables.
    set p' : Polynomial (MvPolynomial (Fin n) R) := finSuccEquiv R n p with hp'
    -- Since `p` is not identically zero, there is some `k` such that `pₖ` is not identically zero.
    -- WLOG `k` is the largest such.
    set k := p'.natDegree with hk
    set pₖ := p'.leadingCoeff with hpₖ
    have hp'₀ : p' ≠ 0 := (AddEquivClass.map_ne_zero_iff _).2 hp
    have hpₖ₀ : pₖ ≠ 0 := by simpa [pₖ, k]
    have hdeg : pₖ.totalDegree + k ≤ p.totalDegree := totalDegree_coeff_finSuccEquiv_add_le _ _ hpₖ₀
    calc
      -- We split the set of possible zeros into a union of two cases.
      #{f ∈ S ^^ (n + 1) | eval f p = 0} / ∏ i, (#S i : ℚ≥0)
          -- In the first case, `pₖ` evaluates to `0`.
        = #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pₖ = 0} / ∏ i, (#S i : ℚ≥0)
          -- In the second case, `pₖ` does not evaluate to `0`.
          + #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pₖ ≠ 0} / ∏ i, (#S i : ℚ≥0) := by
        rw [← add_div, ← Nat.cast_add, ← card_union_add_card_inter, filter_union_right,
          ← filter_and]
        simp [← and_or_left, em, and_and_and_comm]
      _ ≤ ∑ i, (p.degreeOf (.succ i) / #S (.succ i) : ℚ≥0) + p.degreeOf 0 / #S 0 := by
        gcongr ?_ + ?_
        · -- We bound the size of the first set by induction
          calc
            #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pₖ = 0} / ∏ i, (#S i : ℚ≥0)
              ≤ #{r ∈ S ^^ (n + 1) | eval (tail r) pₖ = 0} / ∏ i, (#S i : ℚ≥0) := by
              gcongr; exact fun r hr ↦ hr.2
            _ = #S 0 * #{r ∈ tail S ^^ n | eval r pₖ = 0} / (#S 0 * (∏ i, #S (.succ i) : ℚ≥0)) := by
              rw [card_consEquiv_filter_piFinset S fun f ↦ eval f pₖ = 0, prod_univ_succ, tail_def]
              norm_cast
            _ ≤ #{r ∈ tail S ^^ n | eval r pₖ = 0} / ∏ i, (#S (.succ i) : ℚ≥0) :=
              mul_div_mul_left_le (by positivity)
            _ ≤ ∑ i, (pₖ.degreeOf i / #S (.succ i) : ℚ≥0) := schwartz_zippel hpₖ₀ _
            _ ≤ ∑ i, (p.degreeOf (.succ i) / #S (.succ i) : ℚ≥0) := by
              gcongr; exact degreeOf_coeff_finSuccEquiv ..
        · -- We bound the second set by noting that if `(r, x)` is in it, then `x` is the root of
          -- the univariate polynomial`pᵣ` obtained by evaluating each (multivariate polynomial)
          -- coefficient at `r`. Since `pᵣ` has degree `i`, there are at most `i` such `x` for each
          -- `r`, which gives the result.
          calc
            #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pₖ ≠ 0} / ∏ i, (#S i : ℚ≥0)
              ≤ ↑(p.degreeOf 0 * ∏ i, #S (.succ i)) / ∏ i, (#S i : ℚ≥0) := ?_
            _ = p.degreeOf 0 * (∏ i, #S (.succ i)) / (#S 0 * ∏ i, #S (.succ i)) := by
              norm_cast; rw [prod_univ_succ]
            _ ≤ (p.degreeOf 0 / #S 0 : ℚ≥0) := mul_div_mul_right_le (by positivity) (by positivity)
          gcongr
          calc
            #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pₖ ≠ 0}
              = #{r ∈ S ^^ (n + 1) | eval (tail r) pₖ ≠ 0 ∧ eval r p = 0} := by simp_rw [and_comm]
            _ = #({r ∈ tail S ^^ n | eval r pₖ ≠ 0}.biUnion fun r ↦ image (fun x ↦ (x, r))
                  {x ∈ S 0 | eval (cons x r) p = 0}) := by
              rw [← filter_filter, filter_piFinset_eq_map_consEquiv S (fun r ↦ eval r pₖ ≠ 0),
                filter_map, card_map, product_eq_biUnion_right, filter_biUnion]
              simp [Function.comp_def, Finset.filter_image, filter_filter]
              rfl
            _ ≤ ∑ r ∈ tail S ^^ n with eval r pₖ ≠ 0,
                  #(image (fun x ↦ (x, r)) {x ∈ S 0 | eval (cons x r) p = 0}) := card_biUnion_le
            _ ≤ ∑ r ∈ tail S ^^ n with eval r pₖ ≠ 0, #{x ∈ S 0 | eval (cons x r) p = 0} := by
              gcongr; exact card_image_le
            _ ≤ ∑ r ∈ tail S ^^ n with eval r pₖ ≠ 0, p.degreeOf 0 := ?_
            _ ≤ ∑ _r ∈ tail S ^^ n, p.degreeOf 0 := by gcongr; exact filter_subset ..
            _ = p.degreeOf 0 * ∏ i, #S (.succ i) := by simp [mul_comm, tail]
          gcongr with r hr
          simp at hr
          set pᵣ := p'.map (eval r) with hpᵣ
          have hpᵣdeg : pᵣ.natDegree = k := by
            rw [hpᵣ, hk, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (eval r) hr.2]
          have hpᵣ₀ : pᵣ ≠ 0 := fun h ↦ hr.2 <| by
            rw [hpₖ, Polynomial.leadingCoeff, ← hk, ← hpᵣdeg, h, Polynomial.natDegree_zero,
              ← Polynomial.coeff_map, ← hpᵣ, h, Polynomial.coeff_zero]
          calc
            #{x ∈ S 0 | eval (cons x r) p = 0} ≤ #pᵣ.roots.toFinset := by
              gcongr
              simp (config := { contextual := true}) [subset_iff, eval_eq_eval_mv_eval', pᵣ, hpᵣ₀]
            _ ≤ Multiset.card pᵣ.roots := pᵣ.roots.toFinset_card_le
            _ ≤ pᵣ.natDegree := pᵣ.card_roots'
            _ = k := hpᵣdeg
            _ ≤ p.degreeOf 0 := by
              have :
                (ofLex (AddMonoidAlgebra.supDegree toLex p'.leadingCoeff)).cons k ∈ p.support := by
                rwa [← support_coeff_finSuccEquiv, mem_support_iff, ← hp', hk,
                  ← Polynomial.leadingCoeff, ← hpₖ, ← leadingCoeff_toLex,
                  AddMonoidAlgebra.leadingCoeff_ne_zero toLex.injective]
              simpa using monomial_le_degreeOf 0 this
      _ = ∑ i, (p.degreeOf i / #S i : ℚ≥0) := by rw [sum_univ_succ, add_comm]

end MvPolynomial
