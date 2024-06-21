/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Torsion points on Weierstrass curves
-/

open Polynomial PolynomialPolynomial

universe u v

namespace MonoidHom

open scoped Pointwise

variable {G : Type u} [Group G] {H : Type v} [Group H] (f : G →* H)

@[to_additive]
lemma fiber_equiv_smul_ker (g : G) : f ⁻¹' {f g} = g • f.ker := Set.ext fun _ => by
  erw [Set.mem_singleton_iff, eq_comm, Set.mem_smul_set_iff_inv_smul_mem, mem_ker, map_mul, map_inv,
    inv_mul_eq_one]

@[to_additive (attr := simps!)]
def fiberEquivKer (g : G) : f ⁻¹' {f g} ≃ f.ker :=
  (Equiv.setCongr <| f.fiber_equiv_smul_ker g).trans <| Subgroup.leftCosetEquivSubgroup g

variable {f} (hf : Function.Surjective f)

@[to_additive]
noncomputable def fiberEquivKerOfSurjective (h : H) : f ⁻¹' {h} ≃ f.ker :=
  (hf h).choose_spec ▸ f.fiberEquivKer (hf h).choose

@[to_additive]
noncomputable def fiberEquivOfSurjective (h h' : H) : f ⁻¹' {h} ≃ f ⁻¹' {h'} :=
  (fiberEquivKerOfSurjective hf h).trans (fiberEquivKerOfSurjective hf h').symm

end MonoidHom

namespace Polynomial

variable {R : Type u} [CommSemiring R] (x y : R) (p : R[X][Y])

noncomputable def evalEval : R :=
  (p.eval <| C y).eval x

lemma evalEval_C (p : R[X]) : (C p).evalEval x y = p.eval x := by
  rw [evalEval, eval_C]

@[simps!]
noncomputable def evalEvalRingHom : R[X][Y] →+* R :=
  (evalRingHom x).comp <| evalRingHom <| C y

lemma coe_evalEvalRingHom : evalEvalRingHom x y = evalEval x y :=
  rfl

lemma evalEvalRingHom_eq : evalEvalRingHom x = eval₂RingHom (evalRingHom x) := by
  ext <;> simp

lemma eval₂_evalRingHom : eval₂ (evalRingHom x) y p = p.evalEval x y := by
  rw [← coe_evalEvalRingHom, evalEvalRingHom_eq, coe_eval₂RingHom]

lemma map_evalRingHom_eval : (p.map <| evalRingHom x).eval y = p.evalEval x y := by
  rw [eval_map, eval₂_evalRingHom]

end Polynomial

variable {R : Type u} [CommRing R] {x y : R} {p : R[X][Y]} (h : p.evalEval x y = 0)

namespace AdjoinRoot

@[simps!]
def evalEval : AdjoinRoot p →+* R :=
  lift (evalRingHom x) y <| eval₂_evalRingHom x y p ▸ h

lemma evalEval_eq (g : R[X][Y]) : evalEval h (mk p g) = g.evalEval x y := by
  erw [AdjoinRoot.lift_mk, eval₂_evalRingHom]

end AdjoinRoot

namespace WeierstrassCurve

protected noncomputable def ω (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] :=
  sorry

lemma Affine.CoordinateRing.mk_ψ (W : WeierstrassCurve R) (n : ℤ) :
    mk W (W.ψ n) = mk W (W.Ψ n) := by
  sorry

lemma evalEval_ψ (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y := by
  rw [← AdjoinRoot.evalEval_eq h, Affine.CoordinateRing.mk_ψ W n, AdjoinRoot.evalEval_eq h]

lemma Affine.CoordinateRing.mk_φ (W : WeierstrassCurve R) (n : ℤ) :
    mk W (W.φ n) = mk W (C <| W.Φ n) := by
  sorry

lemma evalEval_φ (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [← AdjoinRoot.evalEval_eq h, Affine.CoordinateRing.mk_φ W n, AdjoinRoot.evalEval_eq h,
    evalEval_C]

namespace Jacobian

lemma comp_fin3 {S : Type v} (f : R → S) (x y z : R) : f ∘ ![x, y, z] = ![f x, f y, f z] :=
  (FinVec.map_eq ..).symm

variable {F : Type v} [Field F] {W : Jacobian F}

lemma equiv_zero_iff_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≈ ![1, 1, 0] ↔ P 2 = 0 :=
  ⟨fun h => (Z_eq_zero_of_equiv h).mpr rfl, equiv_zero_of_Z_eq_zero hP⟩

lemma equiv_zero_or_equiv_some {P : Fin 3 → F} (hP : W.Nonsingular P) :
    P ≈ ![1, 1, 0] ∨ P ≈ ![P 0 / P 2 ^ 2, P 1 / P 2 ^ 3, 1] := by
  by_cases hPz : P 2 = 0
  · exact Or.inl <| (equiv_zero_iff_Z_eq_zero hP).mpr hPz
  · exact Or.inr <| equiv_some_of_Z_ne_zero hPz

lemma eq_zero_or_eq_some {P : PointClass F} (hP : W.NonsingularLift P) :
    P = ⟦![1, 1, 0]⟧ ∨ ∃ x y : F, P = ⟦![x, y, 1]⟧ := by
  rcases P with ⟨P⟩
  rcases equiv_zero_or_equiv_some hP with hP | hP
  · exact Or.inl <| Quotient.eq.mpr hP
  · exact Or.inr ⟨_, _, Quotient.eq.mpr hP⟩

namespace Point

lemma eq_zero_or_eq_some (P : W.Point) : P = 0 ∨ ∃ x y : F, P.point = ⟦![x, y, 1]⟧ := by
  simpa only [Point.ext_iff] using Jacobian.eq_zero_or_eq_some P.nonsingular

lemma nonsingular_zsmul (P : W.Point) (n : ℤ) : W.NonsingularLift (n • P).point := by
  induction n using Int.negInduction with
  | nat n => induction n with
    | zero => simp [zero_point, nonsingularLift_zero]
    | succ _ h => simp only [Nat.cast_add, Nat.cast_one, _root_.add_smul, one_smul, add_point,
      nonsingularLift_addMap h P.nonsingular]
  | neg _ h => simp only [_root_.neg_smul, neg_point, nonsingularLift_negMap h]

theorem zsmul {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) (n : ℤ) :
    (n • mk h).point = ⟦evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]⟧ := by
  sorry

lemma zsmul_mk_eq_zero_iff {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) (n : ℤ) :
    n • mk h = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  rw [Point.ext_iff, zsmul, zero_point, Quotient.eq]
  exact equiv_zero_iff_Z_eq_zero <| zsmul h n ▸ nonsingular_zsmul (mk h) n

end Point

end Jacobian

end WeierstrassCurve
