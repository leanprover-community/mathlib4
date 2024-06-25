/-
Copyright (c) 2024 .... All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ...
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.EllipticCurve.Group

universe u v

open Polynomial PolynomialPolynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] {x y : R} {p : R[X][Y]}

noncomputable abbrev Polynomial.evalEval (x y : R) (p : R[X][Y]) : R :=
  Polynomial.eval x (Polynomial.eval (Polynomial.C y) p)

@[simps!] noncomputable abbrev evalEvalRingHom (x y : R) : R[X][Y] →+* R :=
  (evalRingHom x).comp (evalRingHom <| C y)

lemma coe_evalEvalRingHom (x y : R) : evalEvalRingHom x y = evalEval x y := rfl

lemma evalEvalRingHom_eq (x : R) :
    evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp

lemma eval₂_evalRingHom (x : R) : eval₂ (evalRingHom x) = evalEval x := by
  ext1; rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]

lemma map_mapRingHom_eval_map (f : R →+* S) (q : R[X]) :
    (p.map <| mapRingHom f).eval (q.map f) = (p.eval q).map f := by
  rw [eval_map, ← coe_mapRingHom, eval₂_hom]

lemma map_mapRingHom_eval_map_eval (f : R →+* S) (q : R[X]) (r : R) :
    ((p.map <| mapRingHom f).eval <| q.map f).eval (f r) = f ((p.eval q).eval r) := by
  rw [map_mapRingHom_eval_map, eval_map, eval₂_hom]

lemma map_mapRingHom_evalEval (f : R →+* S) (x y : R) :
    (p.map <| mapRingHom f).evalEval (f x) (f y) = f (p.evalEval x y) := by
  rw [evalEval, ← map_mapRingHom_eval_map_eval, map_C]

namespace AdjoinRoot

@[simps!]
def evalEval (h : p.evalEval x y = 0) : AdjoinRoot p →+* R :=
  lift (evalRingHom x) y <| eval₂_evalRingHom x ▸ h

lemma evalEval_eq (h : p.evalEval x y = 0) (g : R[X][Y]) :
    evalEval h (mk p g) = g.evalEval x y := by
  erw [AdjoinRoot.lift_mk, eval₂_evalRingHom]

end AdjoinRoot

variable {W : WeierstrassCurve.Affine R} {x y : R} (h : W.Equation x y) (f : R →+* S)

lemma WeierstrassCurve.Affine.Equation.map (h : W.Equation x y) :
    Equation (W.map f) (f x) (f y) := by
  sorry

namespace WeierstrassCurve.Affine.CoordinateRing

noncomputable def eval : W.CoordinateRing →+* R :=
  AdjoinRoot.lift (evalRingHom x) y <| by rwa [eval₂_evalRingHom]

lemma eval_mk (p : R[X][Y]) : eval h (mk _ p) = p.evalEval x y := by
  rw [← eval₂_evalRingHom]; exact AdjoinRoot.lift_mk _ p

lemma eval_comp_mk : (eval h).comp (mk _) = evalEvalRingHom x y := RingHom.ext (eval_mk h)

lemma eval_map (p : W.CoordinateRing) : eval (h.map f) (map W f p) = f (eval h p) := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective p
  rw [map_mk, eval_mk, eval_mk, map_mapRingHom_evalEval]

lemma eval_comp_map : (eval <| h.map f).comp (map W f) = f.comp (eval h) :=
  RingHom.ext (eval_map h f)

end WeierstrassCurve.Affine.CoordinateRing

namespace AlgebraicGeometry

variable (W)
noncomputable def AffineWeierstrassCurve : Scheme :=
  Spec <| CommRingCat.of <| W.CoordinateRing

-- Spec R[W] as an object of Sch / Spec R
noncomputable def AffineWeierstrassCurve.map :
    Scheme.Hom (AffineWeierstrassCurve W) (Spec <| CommRingCat.of R) :=
  Spec.map <| CommRingCat.ofHom <| algebraMap R <| WeierstrassCurve.Affine.CoordinateRing W

variable (R) in
private noncomputable abbrev overRing : Type (u + 1) :=
  CategoryTheory.Over (Spec <| CommRingCat.of R)

noncomputable def AffineWeierstrassCurveOver : overRing R :=
  CategoryTheory.Over.mk <| AffineWeierstrassCurve.map W

variable (A : Type u) [CommRing A] [Algebra R A]

-- Spec A as an object of Sch / Spec R
private noncomputable def temp : overRing R :=
  CategoryTheory.Over.mk <| Spec.map <| CommRingCat.ofHom <| algebraMap R A

-- Hom_{Sch / Spec R}(Spec A, Spec R[W])
def AffineWeierstrassCurvePoint : Type u :=
  temp A ⟶ AffineWeierstrassCurveOver W

open WeierstrassCurve.Affine

-- Hom_{R-Alg}(R[W], A)
def equiv : AffineWeierstrassCurvePoint W A ≃ (CoordinateRing W →ₐ[R] A) := by
  sorry

variable {W A} in
noncomputable def ringHom {x y : A} (h : (W.baseChange A).toAffine.Equation x y) :
    CoordinateRing W →+* A :=
  (CoordinateRing.eval h).comp <| CoordinateRing.map W <| algebraMap R A

variable {W A} in
@[simps!]
noncomputable def algHom {x y : A} (h : (W.baseChange A).toAffine.Equation x y) :
    CoordinateRing W →ₐ[R] A :=
  AlgHom.mk (ringHom h) <| by
    intro
    simp
    rw [ringHom, RingHom.comp_apply, CoordinateRing.map]
    -- missing API
    sorry

variable (E : EllipticCurve R)

noncomputable def equiv' [Nontrivial A] :
    Option (CoordinateRing E.toWeierstrassCurve →ₐ[R] A) ≃ E.toWeierstrassCurve⟮A⟯ where
  toFun P := match P with
    | none => 0
    | some f => .some
      (x := f <| WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve <| C X)
      (y := f <| WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve X) <| by
        apply EllipticCurve.Affine.nonsingular <| E.baseChange A
        -- missing API
        sorry
  invFun P := match P with
    | 0 => none
    | .some h => some <| algHom h.left
  left_inv := by
    rintro (_ | _)
    rfl
    simp
    ext
    simp
    -- missing API
    sorry
  right_inv := by
    rintro (_ | _)
    rfl
    simp
    -- missing API
    sorry

noncomputable example [Nontrivial A] :
    Option (AffineWeierstrassCurvePoint E.toWeierstrassCurve A) ≃ E.toWeierstrassCurve⟮A⟯ :=
  (Equiv.optionCongr <| equiv E.toWeierstrassCurve A).trans <| equiv' A E

end AlgebraicGeometry
