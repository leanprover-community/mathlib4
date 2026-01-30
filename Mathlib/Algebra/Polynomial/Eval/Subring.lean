/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Evaluation of polynomials in subrings

## Main results

* `mem_map_rangeS`, `mem_map_range`: the range of `mapRingHom f` consists of
  polynomials with coefficients in the range of `f`

-/

public section

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]} [Semiring S]
variable (f : R →+* S)

theorem mem_map_rangeS {p : S[X]} : p ∈ (mapRingHom f).rangeS ↔ ∀ n, p.coeff n ∈ f.rangeS := by
  constructor
  · rintro ⟨p, rfl⟩ n
    rw [coe_mapRingHom, coeff_map]
    exact Set.mem_range_self _
  · intro h
    rw [p.as_sum_range_C_mul_X_pow]
    refine (mapRingHom f).rangeS.sum_mem ?_
    intro i _hi
    rcases h i with ⟨c, hc⟩
    use C c * X ^ i
    rw [coe_mapRingHom, Polynomial.map_mul, map_C, hc, Polynomial.map_pow, map_X]

theorem mem_map_range {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {p : S[X]} :
    p ∈ (mapRingHom f).range ↔ ∀ n, p.coeff n ∈ f.range :=
  mem_map_rangeS f

end Polynomial
