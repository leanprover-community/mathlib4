/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Oliver Nash
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Identities
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Newton-Raphson method

Given a single-variable polynomial `P` with derivative `P'`, Newton's method concerns iteration of
the rational map: `x ↦ x - P(x) / P'(x)`.

Over a field it can serve as a root-finding algorithm. It is also useful tool in certain proofs
such as Hensel's lemma and Jordan-Chevalley decomposition.

## Main definitions / results:

* `Polynomial.newtonMap`: the map `x ↦ x - P(x) / P'(x)`, where `P'` is the derivative of the
  polynomial `P`.
* `Polynomial.isFixedPt_newtonMap_of_isUnit_iff`: `x` is a fixed point for Newton iteration iff
  it is a root of `P` (provided `P'(x)` is a unit).
* `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`: if `x` is almost a root of `P` in the
  sense that `P(x)` is nilpotent (and `P'(x)` is a unit) then we may write `x` as a sum
  `x = n + r` where `n` is nilpotent and `r` is a root of `P`. This can be used to prove the
  Jordan-Chevalley decomposition of linear endomorphims.

-/

open Set Function

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {x : S}

/-- Given a single-variable polynomial `P` with derivative `P'`, this is the map:
`x ↦ x - P(x) / P'(x)`. When `P'(x)` is not a unit we use a junk-value pattern and send `x ↦ x`. -/
def newtonMap (x : S) : S :=
  x - (Ring.inverse <| aeval x (derivative P)) * aeval x P

theorem newtonMap_apply :
    P.newtonMap x = x - (Ring.inverse <| aeval x (derivative P)) * (aeval x P) :=
  rfl

variable {P}

theorem newtonMap_apply_of_isUnit (h : IsUnit <| aeval x (derivative P)) :
    P.newtonMap x = x - h.unit⁻¹ * aeval x P := by
  simp [newtonMap_apply, Ring.inverse, h]

theorem newtonMap_apply_of_not_isUnit (h : ¬ (IsUnit <| aeval x (derivative P))) :
    P.newtonMap x = x := by
  simp [newtonMap_apply, Ring.inverse, h]

theorem isNilpotent_iterate_newtonMap_sub_of_isNilpotent (h : IsNilpotent <| aeval x P) (n : ℕ) :
    IsNilpotent <| P.newtonMap^[n] x - x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ', comp_apply, newtonMap_apply, sub_right_comm]
    refine (Commute.all _ _).isNilpotent_sub ih <| (Commute.all _ _).isNilpotent_mul_left ?_
    simpa using Commute.isNilpotent_add (Commute.all _ _)
      (isNilpotent_aeval_sub_of_isNilpotent_sub P ih) h

theorem isFixedPt_newtonMap_of_aeval_eq_zero (h : aeval x P = 0) :
    IsFixedPt P.newtonMap x := by
  rw [IsFixedPt, newtonMap_apply, h, mul_zero, sub_zero]

theorem isFixedPt_newtonMap_of_isUnit_iff (h : IsUnit <| aeval x (derivative P)) :
    IsFixedPt P.newtonMap x ↔ aeval x P = 0 := by
  rw [IsFixedPt, newtonMap_apply, sub_eq_self, Ring.inverse_mul_eq_iff_eq_mul _ _ _ h, mul_zero]

/-- This is really an auxiliary result, en route to
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`. -/
theorem aeval_pow_two_pow_dvd_aeval_iterate_newtonMap
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) (n : ℕ) :
    (aeval x P) ^ (2 ^ n) ∣ aeval (P.newtonMap^[n] x) P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ⟨d, hd⟩ := binomExpansion (P.map (algebraMap R S)) (P.newtonMap^[n] x)
      (-Ring.inverse (aeval (P.newtonMap^[n] x) <| derivative P) * aeval (P.newtonMap^[n] x) P)
    rw [eval_map_algebraMap, eval_map_algebraMap] at hd
    rw [iterate_succ', comp_apply, newtonMap_apply, sub_eq_add_neg, neg_mul_eq_neg_mul, hd]
    refine dvd_add ?_ (dvd_mul_of_dvd_right ?_ _)
    · convert dvd_zero _
      have : IsUnit (aeval (P.newtonMap^[n] x) <| derivative P) :=
        isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' <|
        isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n
      rw [derivative_map, eval_map_algebraMap, ← mul_assoc, mul_neg, Ring.mul_inverse_cancel _ this,
        neg_mul, one_mul, add_neg_cancel]
    · rw [neg_mul, even_two.neg_pow, mul_pow, pow_succ, pow_mul]
      exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ih 2) _

/-- If `x` is almost a root of `P` in the sense that `P(x)` is nilpotent (and `P'(x)` is a
unit) then we may write `x` as a sum `x = n + r` where `n` is nilpotent and `r` is a root of `P`.
Moreover, `n` and `r` are unique.

This can be used to prove the Jordan-Chevalley decomposition of linear endomorphims. -/
theorem existsUnique_nilpotent_sub_and_aeval_eq_zero
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) :
    ∃! r, IsNilpotent (x - r) ∧ aeval r P = 0 := by
  simp_rw [(neg_sub _ x).symm, isNilpotent_neg_iff]
  refine existsUnique_of_exists_of_unique ?_ fun r₁ r₂ ⟨hr₁, hr₁'⟩ ⟨hr₂, hr₂'⟩ ↦ ?_
  · -- Existence
    obtain ⟨n, hn⟩ := id h
    refine ⟨P.newtonMap^[n] x, isNilpotent_iterate_newtonMap_sub_of_isNilpotent h n, ?_⟩
    rw [← zero_dvd_iff, ← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
    exact aeval_pow_two_pow_dvd_aeval_iterate_newtonMap h h' n
  · -- Uniqueness
    have ⟨u, hu⟩ := binomExpansion (P.map (algebraMap R S)) r₁ (r₂ - r₁)
    suffices IsUnit (aeval r₁ (derivative P) + u * (r₂ - r₁)) by
      rwa [derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap,
        add_sub_cancel, hr₂', hr₁', zero_add, pow_two, ← mul_assoc, ← add_mul, eq_comm,
        this.mul_right_eq_zero, sub_eq_zero, eq_comm] at hu
    have : IsUnit (aeval r₁ (derivative P)) :=
      isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' hr₁
    rw [← sub_sub_sub_cancel_right r₂ r₁ x]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact (Commute.all _ _).isNilpotent_mul_left <| (Commute.all _ _).isNilpotent_sub hr₂ hr₁

end Polynomial
