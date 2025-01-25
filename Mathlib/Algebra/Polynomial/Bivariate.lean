/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.RingTheory.AdjoinRoot

/-!
# Bivariate polynomials

This file introduces the notation `R[X][Y]` for the polynomial ring `R[X][X]` in two variables,
and the notation `Y` for the second variable, in the `Polynomial` scope.

It also defines `Polynomial.evalEval` for the evaluation of a bivariate polynomial at a point
on the affine plane, which is a ring homomorphism (`Polynomial.evalEvalRingHom`), as well as
the abbreviation `CC` to view a constant in the base ring `R` as a bivariate polynomial.
-/

/-- The notation `Y` for `X` in the `Polynomial` scope. -/
scoped[Polynomial.Bivariate] notation3:max "Y" => Polynomial.X (R := Polynomial _)

/-- The notation `R[X][Y]` for `R[X][X]` in the `Polynomial` scope. -/
scoped[Polynomial.Bivariate] notation3:max R "[X][Y]" => Polynomial (Polynomial R)

open scoped Polynomial.Bivariate

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

@[simp]
lemma evalEval_CC (x y : R) (p : R) : (CC p).evalEval x y = p := by
  rw [evalEval_C, eval_C]

@[simp]
lemma evalEval_zero (x y : R) : (0 : R[X][Y]).evalEval x y = 0 := by
  simp only [evalEval, eval_zero]

@[simp]
lemma evalEval_one (x y : R) : (1 : R[X][Y]).evalEval x y = 1 := by
  simp only [evalEval, eval_one]

@[simp]
lemma evalEval_natCast (x y : R) (n : ℕ) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_natCast]

@[simp]
lemma evalEval_X (x y : R) : X.evalEval x y = y := by
  rw [evalEval, eval_X, eval_C]

@[simp]
lemma evalEval_add (x y : R) (p q : R[X][Y]) :
    (p + q).evalEval x y = p.evalEval x y + q.evalEval x y := by
  simp only [evalEval, eval_add]

lemma evalEval_sum (x y : R) (p : R[X]) (f : ℕ → R → R[X][Y]) :
    (p.sum f).evalEval x y = p.sum fun n a => (f n a).evalEval x y := by
  simp only [evalEval, eval, eval₂_sum]

lemma evalEval_finset_sum {ι : Type*} (s : Finset ι) (x y : R) (f : ι → R[X][Y]) :
    (∑ i ∈ s, f i).evalEval x y = ∑ i ∈ s, (f i).evalEval x y := by
  simp only [evalEval, eval_finset_sum]

@[simp]
lemma evalEval_smul [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (x y : R) (s : S)
    (p : R[X][Y]) : (s • p).evalEval x y = s • p.evalEval x y := by
  simp only [evalEval, eval_smul]

lemma evalEval_surjective (x y : R) : Function.Surjective <| evalEval x y :=
  fun y => ⟨CC y, evalEval_CC ..⟩

end Semiring

section Ring

variable [Ring R]

@[simp]
lemma evalEval_neg (x y : R) (p : R[X][Y]) : (-p).evalEval x y = -p.evalEval x y := by
  simp only [evalEval, eval_neg]

@[simp]
lemma evalEval_sub (x y : R) (p q : R[X][Y]) :
    (p - q).evalEval x y = p.evalEval x y - q.evalEval x y := by
  simp only [evalEval, eval_sub]

@[simp]
lemma evalEval_intCast (x y : R) (n : ℤ) : (n : R[X][Y]).evalEval x y = n := by
  simp only [evalEval, eval_intCast]

end Ring

section CommSemiring

variable [CommSemiring R]

@[simp]
lemma evalEval_mul (x y : R) (p q : R[X][Y]) :
    (p * q).evalEval x y = p.evalEval x y * q.evalEval x y := by
  simp only [evalEval, eval_mul]

lemma evalEval_prod {ι : Type*} (s : Finset ι) (x y : R) (p : ι → R[X][Y]) :
    (∏ j ∈ s, p j).evalEval x y = ∏ j ∈ s, (p j).evalEval x y := by
  simp only [evalEval, eval_prod]

lemma evalEval_list_prod (x y : R) (l : List R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simpa only [evalEval, eval_list_prod, List.map_map] using by rfl

lemma evalEval_multiset_prod (x y : R) (l : Multiset R[X][Y]) :
    l.prod.evalEval x y = (l.map <| evalEval x y).prod := by
  simpa only [evalEval, eval_multiset_prod, Multiset.map_map] using by rfl

@[simp]
lemma evalEval_pow (x y : R) (p : R[X][Y]) (n : ℕ) : (p ^ n).evalEval x y = p.evalEval x y ^ n := by
  simp only [evalEval, eval_pow]

lemma evalEval_dvd (x y : R) {p q : R[X][Y]} : p ∣ q → p.evalEval x y ∣ q.evalEval x y :=
  eval_dvd ∘ eval_dvd

lemma coe_algebraMap_eq_CC : algebraMap R R[X][Y] = CC (R := R) := rfl

/-- `evalEval x y` as a ring homomorphism. -/
@[simps!] abbrev evalEvalRingHom (x y : R) : R[X][Y] →+* R :=
  (evalRingHom x).comp (evalRingHom <| C y)

lemma coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y := rfl

lemma evalEvalRingHom_eq (x : R) : evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp

lemma eval₂_evalRingHom (x : R) : eval₂ (evalRingHom x) = evalEval x := by
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

end AdjoinRoot
