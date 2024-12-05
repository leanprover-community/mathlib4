/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
/-!
# Jacobson radical of polynomial ring

-/

namespace Ideal

section Polynomial

open Polynomial

variable {R : Type*} [CommRing R]

theorem jacobson_bot_polynomial_le_sInf_map_maximal :
    jacobson (⊥ : Ideal R[X]) ≤ sInf (map (C : R →+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  haveI : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson ≤ J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
  have r1 : (X : (R ⧸ j)[X]) ≠ 0 := fun hX => by
    replace hX := congr_arg (fun f => coeff f 1) hX
    simp only [coeff_X_one, coeff_zero] at hX
    exact zero_ne_one hX.symm
  have r2 := eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))
  simp only [coeff_add, mul_coeff_zero, coeff_X_zero, mul_zero, coeff_one_zero, zero_add] at r2
  erw [add_left_eq_self] at r2
  simpa using (mul_eq_zero.mp r2).resolve_right r1
  -- Porting note: this is golfed to much
  -- simpa [(fun hX => by simpa using congr_arg (fun f => coeff f 1) hX : (X : (R ⧸ j)[X]) ≠ 0)]
  --   using eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit ((mem_jacobson_bot.1 hf) X))

theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
    jacobson (⊥ : Ideal R[X]) = ⊥ := by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
  refine fun f hf => (Submodule.mem_bot R[X]).2 <| Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n ∈ Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

end Polynomial

end Ideal
