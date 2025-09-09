/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
import Mathlib.RingTheory.Polynomial.Chebyshev.Real
import Mathlib.LinearAlgebra.Lagrange

/-!
# Chebyshev polynomials over the reals: leading coefficient

## Main statements

* Chebyshev polynomials minimize deviation from zero
-/

namespace Polynomial

open Finset

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι] {s : Finset ι}

theorem C_prod (c : ι → F) :
  ∏ i ∈ s, C (c i) = C (∏ i ∈ s, (c i)) := by
  induction s using Finset.induction
  case empty => simp
  case insert a t ha hind =>
    rw [prod_insert ha, hind, prod_insert ha, C_mul]

theorem degree_of_linear_product (c : ι → F) :
  (∏ i ∈ s, (X - C (c i))).degree = ↑(s.card) := by
  induction s using Finset.induction
  case empty => simp
  case insert a t ha hind =>
  rw [prod_insert ha, card_insert_of_notMem ha]
  rw [degree_mul, hind, degree_X_sub_C, add_comm]
  push_cast; rfl

theorem coeff_of_linear_product (c : ι → F) :
  (∏ i ∈ s, (X - C (c i))).coeff #s = 1 := by
  induction s using Finset.induction
  case empty => simp
  case insert a t ha hind =>
  rw [prod_insert ha, card_insert_of_notMem ha]
  rw [sub_mul, coeff_sub, coeff_X_mul, hind, coeff_C_mul]
  suffices (∏ i ∈ t, (X - C (c i))).coeff (#t + 1) = 0 by simp [this]
  apply coeff_eq_zero_of_degree_lt
  rw [degree_of_linear_product]
  apply Nat.cast_lt.mpr
  omega

end Polynomial

namespace Lagrange

open Polynomial

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

theorem interpolate_poly [DecidableEq F] {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
  {P : Polynomial F} (hP : P.degree < s.card) :
  (interpolate s v) (fun (i : ι) => P.eval (v i)) = P := by
  let t : Finset F := s.image v
  have ht : t.card = s.card := Finset.card_image_iff.mpr hvs
  apply eq_of_degrees_lt_of_eval_finset_eq t
  · rw [ht]
    apply degree_interpolate_lt _ hvs
  · rw [ht]
    exact hP
  · intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_image.mp hx
    rw [← hx, eval_interpolate_at_node _ hvs hi]

theorem basis_topCoeff {s : Finset ι} {v : ι → F} {i : ι} (hi : i ∈ s) :
  (Lagrange.basis s v i).coeff (s.card - 1) = (∏ j ∈ s.erase i, ((v i) - (v j)))⁻¹ := by
  rw [Lagrange.basis]
  unfold basisDivisor
  rw [Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, C_prod, coeff_C_mul]
  suffices s.card - 1 = (s.erase i).card by
    rw [this, coeff_of_linear_product, mul_one]
  rw [Finset.card_erase_of_mem hi]

theorem interpolate_leadingCoeff [DecidableEq F] (s : Finset ι) (v : ι → F) (hvs : Set.InjOn v s)
  {P : Polynomial F} (hP : s.card = P.degree + 1) :
  P.leadingCoeff = ∑ i ∈ s, (P.eval (v i)) / ∏ j ∈ s.erase i, ((v i) - (v j)) := by
  have P_degree : P.degree = ↑(s.card - 1) := by
    cases h : P.degree
    case bot => rw [h] at hP; simp at hP
    case coe d => rw [h] at hP; simp [ENat.coe_inj.mp hP]; rfl
  have P_natDegree : P.natDegree = s.card - 1 := natDegree_eq_of_degree_eq_some P_degree
  have s_card : s.card > 0 := by
    by_contra! h
    have : s.card = 0 := by omega
    rw [this, P_degree] at hP
    have := ENat.coe_inj.mp hP
    dsimp at this
    omega
  have hP' : P.degree < s.card := by rw [P_degree, Nat.cast_lt]; omega
  rw [leadingCoeff, P_natDegree]
  rw (occs := [1]) [← interpolate_poly hvs hP']
  rw [interpolate_apply, finset_sum_coeff]
  congr! with i hi
  rw [coeff_C_mul, basis_topCoeff hi]
  field_simp

end Lagrange

namespace Polynomial.Chebyshev

open Polynomial
open Real

end Polynomial.Chebyshev
