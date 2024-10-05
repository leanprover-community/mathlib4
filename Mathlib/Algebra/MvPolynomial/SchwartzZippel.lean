/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Yaël Dillies
-/
import Mathlib.Algebra.MvPolynomial.Equiv
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

* Generalize to noncommutative rings? Is that even possible?
* Generalize to subset of the ring being different for each variable.
  * What does the theorem say in this case?
  * Note that the Schwartz paper covers this case
* Reexpress in terms of probabilities.
* Then generalize to polynomials over arbitrary variable types
* Write a tactic to apply this lemma to a given polynomial

## References

* [demillo_lipton_1978]
* [schwartz_1980]
* [zippel_1979]
-/

local prefix:100 "#" => Finset.card
local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

open Fin Finset Fintype MvPolynomial

/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from some finite subset `S` of the integral domain is
bounded by the degree of `p` over `|S|`. This version presents this lemma in terms of `Finset`. -/
lemma schwartz_zippel (F : Type*) [CommRing F] [IsDomain F] [DecidableEq F] :
    ∀ n {p : MvPolynomial (Fin n) F} (_hp : p ≠ 0) (S : Finset F),
      #{f ∈ S ^^ n | eval f p = 0} * #S ≤ p.totalDegree * #S ^ n
  | 0, p, hp, S => by
    -- Because `p` is a polynomial over zero variables, it is constant.
    rw [p.eq_C_of_isEmpty] at *
    simpa using Or.inl hp
    -- Now, assume that the theorem holds for all polynomials in `n` variables.
  | n + 1, p, hp, S => by
    -- We can consider `p` to be a polynomial over multivariable polynomials in one fewer variables.
    set p' : Polynomial (MvPolynomial (Fin n) F) := finSuccEquiv F n p
    -- Since `p` is not identically zero, there is some `i` such that `pᵢ` is not identically zero.
    -- WLOG `i` is the largest such.
    set i := p'.natDegree with hi
    set pᵢ := p'.coeff i with hpᵢ
    have hp'₀ : p' ≠ 0 := (AddEquivClass.map_ne_zero_iff _).2 hp
    have hpᵢ₀ : pᵢ ≠ 0 := by simpa [pᵢ, i]
    have hdeg : pᵢ.totalDegree + i ≤ p.totalDegree := totalDegree_coeff_finSuccEquiv_add_le _ _ hpᵢ₀
    calc
      -- We split the set of possible zeros into a union of two cases.
      #{r ∈ S ^^ (n + 1) | eval r p = 0} * #S
          -- In the first case, pᵢ evaluates to 0.
        = (#{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pᵢ = 0}
          -- In the second case pᵢ does not evaluate to 0.
          + #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pᵢ ≠ 0}) * #S := by
        rw [← card_union_add_card_inter, filter_union_right, ← filter_and]
        simp [← and_or_left, em, and_and_and_comm]
      _ ≤ ((totalDegree p - i) * #S ^ n + i * #S ^ n) * #S := by
        gcongr
        -- We bound the size of the first set by induction
        · calc
          #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pᵢ = 0}
            ≤ #{r ∈ S ^^ (n + 1) | eval (tail r) pᵢ = 0} := by gcongr; exact fun r hr ↦ hr.2
          _ = #{r ∈ S ^^ n | eval r pᵢ = 0} * #S := by
            rw [mul_comm, card_consEquiv_filter_piFinset (fun _ ↦ S) fun f ↦ eval f pᵢ = 0]; rfl
          _ ≤ totalDegree pᵢ * #S ^ n := schwartz_zippel F n hpᵢ₀ S
          _ ≤ (totalDegree p - i) * #S ^ n := by gcongr; exact Nat.le_sub_of_add_le hdeg
          -- We bound the second set by noting that if `(r, x)` is in it, then `x` is the root of
          -- the univariate polynomial`pᵣ` obtained by evaluating each (multivariate polynomial)
          -- coefficient at `r`. Since `pᵣ` has degree `i`, there are at most `i` such `x` for each
          -- `r`, which gives the result.
        · calc
            #{r ∈ S ^^ (n + 1) | eval r p = 0 ∧ eval (tail r) pᵢ ≠ 0}
              = #{r ∈ S ^^ (n + 1) | eval (tail r) pᵢ ≠ 0 ∧ eval r p = 0} := by simp_rw [and_comm]
            _ = #({r ∈ S ^^ n | eval r pᵢ ≠ 0}.biUnion fun r ↦ image (fun x ↦ (x, r))
                  {x ∈ S | eval (cons x r) p = 0}) := by
              rw [← filter_filter, filter_piFinset_eq_map_consEquiv (fun _ ↦ S)
                (fun r ↦ eval r pᵢ ≠ 0), filter_map, card_map, product_eq_biUnion_right,
                filter_biUnion]
              simp [Function.comp_def, Finset.filter_image, filter_filter]
              rfl
            _ ≤ ∑ r ∈ S ^^ n with eval r pᵢ ≠ 0,
                  #(image (fun x ↦ (x, r)) {x ∈ S | eval (cons x r) p = 0}) := card_biUnion_le
            _ ≤ ∑ r ∈ S ^^ n with eval r pᵢ ≠ 0, #{x ∈ S | eval (cons x r) p = 0} := by
              gcongr; exact card_image_le
            _ ≤ ∑ r ∈ S ^^ n with eval r pᵢ ≠ 0, i := ?_
            _ ≤ ∑ _r ∈ S ^^ n, i := by gcongr; exact filter_subset ..
            _ = i * #S ^ n := by simp [mul_comm]
          gcongr with r hr
          simp at hr
          set pᵣ := p'.map (eval r) with hpᵣ
          have hpᵣdeg : pᵣ.natDegree = i := by
            rw [hpᵣ, hi, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (eval r) hr.2]
          have hpᵣ₀ : pᵣ ≠ 0 := fun h ↦ hr.2 <| by
            rw [hpᵢ, ← hpᵣdeg, h, Polynomial.natDegree_zero, ← Polynomial.coeff_map, ← hpᵣ, h,
              Polynomial.coeff_zero]
          calc
            #{x ∈ S | eval (cons x r) p = 0} ≤ pᵣ.roots.toFinset.card := by
              gcongr
              simp (config := { contextual := true}) [subset_iff, eval_eq_eval_mv_eval', pᵣ, hpᵣ₀]
            _ ≤ Multiset.card pᵣ.roots := pᵣ.roots.toFinset_card_le
            _ ≤ pᵣ.natDegree := pᵣ.card_roots'
            _ = i := hpᵣdeg
      _ = totalDegree p * #S ^ (n + 1) := by
        rw [pow_succ, ← mul_assoc, ← add_mul, Nat.sub_add_cancel (le_of_add_le_right hdeg)]
