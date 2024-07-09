/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Algebra.Int
import Mathlib.Algebra.Algebra.Hom.Int
import Mathlib.Algebra.Polynomial.AlgebraMap

#align_import data.polynomial.algebra_map from "leanprover-community/mathlib"@"e064a7bf82ad94c3c17b5128bbd860d1ec34874e"

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/

namespace Polynomial

-- these used to be about `algebraMap ℤ R`, but now the simp-normal form is `Int.castRingHom R`.
@[simp]
theorem ringHom_eval₂_intCastRingHom {R S : Type*} [Ring R] [Ring S] (p : ℤ[X]) (f : R →+* S)
    (r : R) : f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  algHom_eval₂_algebraMap p f.toIntAlgHom r
#align polynomial.ring_hom_eval₂_cast_int_ring_hom Polynomial.ringHom_eval₂_intCastRingHom

@[deprecated (since := "2024-05-27")]
alias ringHom_eval₂_cast_int_ringHom := ringHom_eval₂_intCastRingHom

@[simp]
theorem eval₂_intCastRingHom_X {R : Type*} [Ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f X) p = f p :=
  eval₂_algebraMap_X p f.toIntAlgHom
set_option linter.uppercaseLean3 false in
#align polynomial.eval₂_int_cast_ring_hom_X Polynomial.eval₂_intCastRingHom_X

@[deprecated (since := "2024-04-17")]
alias eval₂_int_castRingHom_X := eval₂_intCastRingHom_X


