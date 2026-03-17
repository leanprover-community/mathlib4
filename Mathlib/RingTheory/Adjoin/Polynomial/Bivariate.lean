/-
Copyright (c) 2026 Xavier Généreux, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Ring.Defs

/-!
# Bivariate polynomials and adjoining transcendental elements

## Main results

* `IsAlgebraic.adjoin_singleton`:
  Given two transcendental elements `a`, `b` over `R`, if one of them, say `a`, is algebraic over
  `R[b]` then `b` is algebraic over `R[a]`.
-/

@[expose] public noncomputable section

namespace Polynomial.Bivariate

open Polynomial Bivariate Algebra Transcendental

variable {R A : Type*} [CommRing R]

section Ring

variable [Ring A] [Algebra R A]

/-- The `AlgEquiv` between `R[X][Y]` and `R[a][Y]` for some transcendental `a`. -/
def equivAdjoinOfTranscendental (x : A) (hx : Transcendental R x) :
    R[X][Y] ≃ₐ[R] (Algebra.adjoin R {x})[X] :=
  mapAlgEquiv (algEquivOfTranscendental _ x hx)

theorem equivAdjoinOfTranscendental_apply {x : A} (hx : Transcendental R x) (p : R[X][Y]) :
    equivAdjoinOfTranscendental x hx p = mapAlgHom (aeval ⟨x, self_mem_adjoin_singleton R x⟩) p :=
  rfl

attribute [local instance] algebra in
theorem equivAdjoinOfTranscendental_swap_eq_aeval {x : A} (hx : Transcendental R x) (p : R[X][Y]) :
    equivAdjoinOfTranscendental x hx (swap p) =
      aeval (C ⟨x, self_mem_adjoin_singleton R x⟩) p := by
  induction p using Polynomial.induction_on' with
  | add => simp_all only [map_add]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add p q => simp_all only [map_add]
    | monomial => simp_all [C_mul_X_pow_eq_monomial, equivAdjoinOfTranscendental]

end Ring

section CommRing

variable [CommRing A] [Algebra R A]

variable {B : Type*} [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

attribute [local instance] Polynomial.algebra in
theorem aeval_aeval_eq_aeval_equivAdjoinOfTranscendental {x : A} (y : B)
    (hx : Transcendental R x) (p : R[X][Y]) :
    aeval (algebraMap A B x) (aeval (C (⟨y, self_mem_adjoin_singleton R y⟩ :
      adjoin R {y})) p) = aeval y (equivAdjoinOfTranscendental x hx p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp_all [map_add]
  | monomial n a =>
    simp_all [aeval_algebraMap_apply, equivAdjoinOfTranscendental, Subalgebra.algebraMap_def]

theorem _root_.IsAlgebraic.adjoin_singleton {x : A} {y : B} (hx : Transcendental R x)
    (hy : Transcendental R y) (h : IsAlgebraic (adjoin R {x}) y) :
    IsAlgebraic (adjoin R {y}) (algebraMap A B x) := by
  obtain ⟨f, hnezero, halg⟩ := h
  refine ⟨(equivAdjoinOfTranscendental y hy) (swap ((equivAdjoinOfTranscendental x hx).symm f)),
    by simpa only [map_ne_zero_iff _ (AlgEquiv.injective _)], ?_⟩
  rw [equivAdjoinOfTranscendental_swap_eq_aeval hy]
  simpa [aeval_aeval_eq_aeval_equivAdjoinOfTranscendental y hx]

end CommRing

end Polynomial.Bivariate

end
