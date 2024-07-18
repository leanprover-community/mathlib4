/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu

-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.QuotientOperations

/-!
# Bivariate polynomials

This file introduces the notation `R[X][Y]` for the polynomial ring `R[X][X]` in two variables,
and the notation `Y` for the second variable, in the `Polynomial` scope.

It also defines `Polynomial.evalEval` for the evaluation of a bivariate polynomial at a point
on the affine plane, which is a ring homomorphism (`Polynomial.evalEvalRingHom`), as well as
the abbreviation `CC` to view a constant in the base ring `R` as a bivariate polynomial.
-/

/-- The notation `Y` for `X` in the `Polynomial` scope. -/
scoped[Polynomial] notation3:max "Y" => Polynomial.X (R := Polynomial _)

/-- The notation `R[X][Y]` for `R[X][X]` in the `Polynomial` scope. -/
scoped[Polynomial] notation3:max R "[X][Y]" => Polynomial (Polynomial R)

namespace Polynomial

noncomputable section
variable {R S : Type*}

section Semiring

variable [Semiring R]

/-- `evalEval x y p` is the evaluation `p(x,y)` of a two-variable polynomial `p : R[X][Y]`. -/
abbrev evalEval (x y : R) (p : R[X][Y]) : R := eval x (eval (C y) p)

/-- A constant viewed as a polynomial in two variables. -/
abbrev CC (r : R) : R[X][Y] := C (C r)

lemma evalEval_C (x y : R) (p : R[X]) : (C p).evalEval x y = p.eval x := by
  rw [evalEval, eval_C]

lemma evalEval_X (x y : R) : X.evalEval x y = y := by
  rw [evalEval, eval_X, eval_C]

lemma evalEval_CC (x y z : R) : (CC z).evalEval x y = z := by
  rw [evalEval, CC, eval_C, eval_C]

end Semiring

section CommSemiring

variable [CommSemiring R]

lemma coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R := R) := rfl

/-- `evalEval x y` as a ring homomorphism. -/
@[simps!] abbrev evalEvalRingHom (x y : R) : R[X][Y] →+* R :=
  (evalRingHom x).comp (evalRingHom <| C y)

lemma coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y := rfl

lemma evalEvalRingHom_comp_algebraMap (x y : R) :
    (evalEvalRingHom x y).comp (algebraMap R R[X][Y]) = .id _ := by
  ext; apply evalEval_CC

lemma evalEvalRingHom_eq (x : R) :
    evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp

lemma eval₂_evalRingHom (x : R) :
    eval₂ (evalRingHom x) = evalEval x := by
  ext1; rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]

lemma map_evalRingHom_eval (x y : R) (p : R[X][Y]) :
    (p.map <| evalRingHom x).eval y = p.evalEval x y := by
  rw [eval_map, eval₂_evalRingHom]

end CommSemiring

section

variable [Semiring R] [Semiring S] (f : R →+* S) (p : R[X][Y]) (q : R[X])

lemma map_mapRingHom_eval_map : (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f := by
  rw [eval_map, ← coe_mapRingHom, eval₂_hom]

lemma map_mapRingHom_eval_map_eval (r : R) :
    ((p.map <| mapRingHom f).eval <| q.map f).eval (f r) = f ((p.eval q).eval r) := by
  rw [map_mapRingHom_eval_map, eval_map, eval₂_hom]

lemma map_mapRingHom_evalEval (x y : R) :
    (p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y) := by
  rw [evalEval, ← map_mapRingHom_eval_map_eval, map_C]

end

variable [CommSemiring R] [CommSemiring S]

lemma eval₂RingHom_aeval_C_X_Y : eval₂RingHom (aeval <| C X).toRingHom (Y : R[X][Y]) = .id _ := by
  ext <;> simp

lemma eval₂_aeval_C_X_Y (p : R[X][Y]) : eval₂ (aeval <| C X).toRingHom (Y : R[X][Y]) p = p :=
  congr($(eval₂RingHom_aeval_C_X_Y) p)

/-- Two equivalent ways to express the evaluation of a bivariate polynomial over `R`
at a point in the affine plane over an `R`-algebra `S`. -/
lemma eval₂RingHom_eval₂RingHom (f : R →+* S) (x y : S) :
    eval₂RingHom (eval₂RingHom f x) y =
      (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom f) := by
  ext <;> simp

lemma eval₂_eval₂RingHom_apply (f : R →+* S) (x y : S) (p : R[X][Y]) :
    eval₂ (eval₂RingHom f x) y p = (p.map <| mapRingHom f).evalEval x y :=
  congr($(eval₂RingHom_eval₂RingHom f x y) p)

lemma eval_C_X_comp_eval₂_map_C_X :
    (evalRingHom (C X : R[X][Y])).comp (eval₂RingHom (mapRingHom <| algebraMap R R[X][Y]) (C Y)) =
      .id _ := by
  ext <;> simp

/-- Viewing `R[X,Y,X']` as an `R[X']`-algebra, a polynomial `p : R[X',Y']` can be evaluated at
`Y : R[X,Y,X']` (substitution of `Y'` by `Y`), obtaining another polynomial in `R[X,Y,X']`.
When this polynomial is then evaluated at `X' = X`, the original polynomial `p` is recovered. -/
lemma eval_C_X_eval₂_map_C_X {p : R[X][Y]} :
    eval (C X) (eval₂ (mapRingHom <| algebraMap R R[X][Y]) (C Y) p) = p :=
  congr($eval_C_X_comp_eval₂_map_C_X p)

variable {A A'} [CommSemiring A] [CommSemiring A'] [Algebra R A] [Algebra R A']

/-- -/
@[simps!] def aevalAEval (x y : A) : R[X][Y] →ₐ[R] A :=
  .mk (eval₂RingHom (aeval x).toRingHom y) fun r ↦ by simp

lemma aevalAEval_toRingHom (x y : A) :
    (aevalAEval x y).toRingHom =
      (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom <| algebraMap R A) := by
  ext <;> simp

lemma aevalAEval_eq_evalEval (x y : A) (p : R[X][Y]) :
    aevalAEval x y p = evalEval x y (p.map <| mapRingHom <| algebraMap R A) :=
  congr($(aevalAEval_toRingHom x y) p)

lemma evalEvalRingHom_comp_map_mapRingHom_algebraMap {x y : A} :
    (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom <| algebraMap R A) =
      (aevalAEval x y).toRingHom := by
  ext <;> simp

lemma evalEval_map_mapRingHom_algebraMap (x y : A) (p : R[X][Y]) :
    evalEval x y (p.map <| mapRingHom <| algebraMap R A) = aevalAEval x y p :=
  congr($evalEvalRingHom_comp_map_mapRingHom_algebraMap p)

lemma aevalAEval_algHom (f : A →ₐ[R] A') (x y : A) (p : R[X][Y]) :
    aevalAEval (f x) (f y) p = f (aevalAEval x y p) := by
  simp_rw [aevalAEval_eq_evalEval, ← f.comp_algebraMap, ← coe_mapRingHom, ← mapRingHom_comp,
    RingHom.comp_apply, coe_mapRingHom, ← f.coe_toRingHom, map_mapRingHom_evalEval]

lemma aevalAEval_X_Y (p : R[X][Y]): aevalAEval (C X : R[X][Y]) Y p = p := by
  erw [aevalAEval_apply, eval₂_aeval_C_X_Y]

variable (R A) in
/-- -/
@[simps] def algHomPolynomial₂Equiv : (R[X][Y] →ₐ[R] A) ≃ A × A where
  toFun f := (f (C X), f Y)
  invFun xy := aevalAEval xy.1 xy.2
  left_inv f := by ext <;> simp
  right_inv xy := by simp

open Ideal.Quotient in
/-- -/
@[simps] def _root_.quotientIdealSpanSingletonAlgHomEquiv {A'} [CommRing A'] [Algebra R A']
    (a : A') : (A' ⧸ Ideal.span {a} →ₐ[R] A) ≃ {f : A' →ₐ[R] A // f a = 0} where
  toFun f := ⟨f.comp (mkₐ _ _), by simp⟩
  invFun f := Ideal.Quotient.liftₐ _ f fun x hx ↦ by
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, f.2, mul_zero]
  left_inv f := by ext ⟨_⟩; simp
  right_inv f := by ext; simp

end

end Polynomial

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {x y : R} {p : R[X][Y]} (h : p.evalEval x y = 0)

/-- If the evaluation (`evalEval`) of a bivariate polynomial `p : R[X][Y]` at a point (x,y)
is zero, then `Polynomial.evalEval x y` factors through `AdjoinRoot.evalEval`, a ring homomorphism
from `AdjoinRoot p` to `R`. -/
@[simps!] def evalEval : AdjoinRoot p →+* R :=
  lift (evalRingHom x) y <| eval₂_evalRingHom x ▸ h

lemma evalEval_mk (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y := by
  rw [evalEval, lift_mk, eval₂_evalRingHom]

variable (p) {A} [CommSemiring A] [Algebra R A]

suppress_compilation
/-- -/
@[simps!] def algHomEquiv : (AdjoinRoot p →ₐ[R] A) ≃ {xy : A × A // aevalAEval xy.1 xy.2 p = 0} :=
  (quotientIdealSpanSingletonAlgHomEquiv p).trans <| ((algHomPolynomial₂Equiv R A).image _).trans <|
    Equiv.setCongr <| by rw [Equiv.image_eq_preimage]; ext; simp; rfl

@[simps!] def mkₐ (p : R[X]) : R[X] →ₐ[R] AdjoinRoot p where
  __ := mk p
  commutes' := by simp

lemma mkₐ_eq_mk (p : R[X]) : mkₐ p = mk p := rfl
lemma mkₐ_apply_eq (p : R[X]) (x : R[X]) : mkₐ p x = mk p x := rfl

@[simps!] def mkₐ₂ : R[X][Y] →ₐ[R] AdjoinRoot p := (mkₐ p).restrictScalars _

lemma mkₐ₂_eq_mkₐ (p : R[X][Y]) : mkₐ₂ p = mk p := rfl
lemma mkₐ₂_apply_eq (p : R[X][Y]) (x : R[X][Y]) : mkₐ₂ p x = mk p x := rfl


lemma aevalAEval_X_Y : aevalAEval (mk p <| C X) (mk p Y) p = 0 := by
  simp_rw [← mkₐ₂_apply_eq, aevalAEval_algHom, Polynomial.aevalAEval_X_Y, mkₐ₂_apply_eq, mk_self]

end AdjoinRoot
