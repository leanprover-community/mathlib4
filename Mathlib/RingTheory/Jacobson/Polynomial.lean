/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient
/-!
# Jacobson radical of polynomial ring

-/

public section

namespace Ring

open Ideal

section Polynomial

open Polynomial

variable {R : Type*} [CommRing R]

theorem jacobson_polynomial_le_sInf_map_maximal :
    Ring.jacobson R[X] ≤ sInf (Ideal.map (C : R →+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  have : j.IsMaximal := hj.1
  refine Trans.trans ringJacobson_le_jacobson (le_of_eq ?_ : J.jacobson ≤ J)
  suffices t : Ring.jacobson (Polynomial (R ⧸ j)) = ⊥ by
    rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot]
    rw [← Ideal.jacobson_bot] at t ⊢
    replace t := congr(Ideal.map (polynomialQuotientEquivQuotientPolynomial j).toRingHom $t)
    rwa [map_jacobson_of_bijective _, Ideal.map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
  have r1 : (X : (R ⧸ j)[X]) ≠ 0 := ne_of_apply_ne (coeff · 1) <| by simp
  simpa [r1] using
    eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((Ring.mem_jacobson_iff.1 hf) X))

theorem jacobson_polynomial_eq_bot_of_jacobson_eq_bot (h : Ring.jacobson R = ⊥) :
    Ring.jacobson R[X] = ⊥ := by
  refine eq_bot_iff.2 (le_trans Ring.jacobson_polynomial_le_sInf_map_maximal ?_)
  refine fun f hf => (Submodule.mem_bot R[X]).2 <| Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n ∈ Ring.jacobson R by rwa [h, Submodule.mem_bot] at this
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj, rfl⟩⟩)) n

end Polynomial

end Ring

namespace Ideal

open Polynomial

@[deprecated Ring.jacobson_polynomial_le_sInf_map_maximal +typeChanged (since := "2026-10-12")]
theorem jacobson_bot_polynomial_le_sInf_map_maximal {R : Type*} [CommRing R] :
    jacobson (⊥ : Ideal R[X]) ≤
      sInf (map (Polynomial.C : R →+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  simpa only [jacobson_bot] using
    (Ring.jacobson_polynomial_le_sInf_map_maximal (R := R))

@[deprecated Ring.jacobson_polynomial_eq_bot_of_jacobson_eq_bot +typeChanged
  (since := "2026-10-12")]
theorem jacobson_bot_polynomial_of_jacobson_bot {R : Type*} [CommRing R]
    (h : jacobson (⊥ : Ideal R) = ⊥) : jacobson (⊥ : Ideal R[X]) = ⊥ := by
  rw [jacobson_bot] at h ⊢
  exact Ring.jacobson_polynomial_eq_bot_of_jacobson_eq_bot h

end Ideal
