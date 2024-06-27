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

open Polynomial

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

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {F : Type v} [Field F]

protected noncomputable def ω (W : WeierstrassCurve R) (n : ℤ) : R[X][Y] :=
  sorry

namespace Affine

namespace Point

variable (W' : Affine R) (W : Affine F)

def equivOptionSubtypeFun (p : W'.Point → Prop) :
    {P : W'.Point // p P} → Option {xy : R × R // ∃ h : W'.Nonsingular xy.1 xy.2, p <| some h}
  | ⟨zero, _⟩ => none
  | ⟨@some _ _ _ x y h, ph⟩ => .some ⟨⟨x, y⟩, h, ph⟩

@[simps]
def equivOptionSubtype {p : W'.Point → Prop} (p0 : p 0) :
    {P : W'.Point // p P} ≃ Option {xy : R × R // ∃ h : W'.Nonsingular xy.1 xy.2, p <| some h} where
  toFun := equivOptionSubtypeFun W' p
  invFun P := P.casesOn ⟨0, p0⟩ fun xy => ⟨some xy.property.choose, xy.property.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

lemma equivOptionSubtype_zero {p : W'.Point → Prop} (p0 : p 0) :
    equivOptionSubtype W' p0 ⟨0, p0⟩ = none :=
  rfl

variable {W'} in
lemma equivOptionSubtype_some {x y : R} (h : W'.Nonsingular x y) {p : W'.Point → Prop} (p0 : p 0)
    (ph : p <| some h) : equivOptionSubtype W' p0 ⟨some h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

lemma equivOptionSubtype_symm_none {p : W'.Point → Prop} (p0 : p 0) :
    (equivOptionSubtype W' p0).symm none = ⟨0, p0⟩ :=
  rfl

variable {W'} in
lemma equivOptionSubtype_symm_some {x y : R} (h : W'.Nonsingular x y) {p : W'.Point → Prop}
    (p0 : p 0) (ph : p <| some h) :
    (equivOptionSubtype W' p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨some h, ph⟩ :=
  rfl

@[simps!]
def equivOption : W'.Point ≃ Option {xy : R × R // W'.Nonsingular xy.1 xy.2} :=
  (Equiv.Set.univ W'.Point).symm.trans <| (equivOptionSubtype W' trivial).trans
    (Equiv.setCongr <| Set.ext fun _ => exists_iff_of_forall fun _ => trivial).optionCongr

lemma equivOption_zero : equivOption W' 0 = none :=
  rfl

variable {W'} in
lemma equivOption_some {x y : R} (h : W'.Nonsingular x y) :
    equivOption W' (some h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

lemma equivOption_symm_none : (equivOption W').symm none = 0 :=
  rfl

variable {W'} in
lemma equivOption_symm_some {x y : R} (h : W'.Nonsingular x y) :
    (equivOption W').symm (.some ⟨⟨x, y⟩, h⟩) = some h :=
  rfl

def zsmulKerEquivOption (n : ℤ) : (zsmulAddGroupHom n : W.Point →+ W.Point).ker ≃
    Option {xy : F × F | ∃ h : W.Nonsingular xy.1 xy.2, n • some h = 0} :=
  equivOptionSubtype W <| smul_zero n

lemma zsmulKerEquivOption_zero (n : ℤ) : zsmulKerEquivOption W n 0 = none :=
  rfl

variable {W} in
lemma zsmulKerEquivOption_some {n : ℤ} {x y : F} (h : W.Nonsingular x y) (hn : n • some h = 0) :
    zsmulKerEquivOption W n ⟨some h, hn⟩ = .some ⟨⟨x, y⟩, h, hn⟩ :=
  rfl

lemma zsmulKerEquivOption_symm_zero (n : ℤ) : (zsmulKerEquivOption W n).symm none = 0 :=
  rfl

variable {W} in
lemma zsmulKerEquivOption_symm_some {n : ℤ} {x y : F} (h : W.Nonsingular x y)
    (hn : n • some h = 0) : (zsmulKerEquivOption W n).symm (.some ⟨⟨x, y⟩, h, hn⟩) = ⟨some h, hn⟩ :=
  rfl

end Point

end Affine

lemma evalEval_Ψ_sq (W : WeierstrassCurve R) (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    (W.Ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  rw [← AdjoinRoot.evalEval_mk h, ← map_pow, Affine.CoordinateRing.mk_Ψ_sq,
    AdjoinRoot.evalEval_mk h, Polynomial.evalEval_C]

lemma evalEval_ψ (W : WeierstrassCurve R) (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    (W.ψ n).evalEval x y = (W.Ψ n).evalEval x y := by
  rw [← AdjoinRoot.evalEval_mk h, Affine.CoordinateRing.mk_ψ, AdjoinRoot.evalEval_mk h]

lemma evalEval_φ (W : WeierstrassCurve R) (n : ℤ) {x y : R} (h : W.toAffine.Equation x y) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  rw [← AdjoinRoot.evalEval_mk h, Affine.CoordinateRing.mk_φ, AdjoinRoot.evalEval_mk h,
    Polynomial.evalEval_C]

namespace Jacobian

variable {W : Jacobian F}

lemma equiv_zero_iff_Z_eq_zero {P : Fin 3 → F} (hP : W.Nonsingular P) : P ≈ ![1, 1, 0] ↔ P 2 = 0 :=
  ⟨fun h => (Z_eq_zero_of_equiv h).mpr rfl, equiv_zero_of_Z_eq_zero hP⟩

lemma equiv_zero_or_equiv_some {P : Fin 3 → F} (hP : W.Nonsingular P) :
    P ≈ ![1, 1, 0] ∨ P ≈ ![P 0 / P 2 ^ 2, P 1 / P 2 ^ 3, 1] := by
  by_cases hPz : P 2 = 0
  · exact Or.inl <| (equiv_zero_iff_Z_eq_zero hP).mpr hPz
  · exact Or.inr <| equiv_some_of_Z_ne_zero hPz

lemma eq_zero_or_eq_some {P : PointClass F} (hP : W.NonsingularLift P) :
    P = ⟦![1, 1, 0]⟧ ∨ ∃ x y : F, P = ⟦![x, y, 1]⟧ := by
  rcases P
  exact (equiv_zero_or_equiv_some hP).casesOn (Or.inl ∘ Quotient.eq.mpr)
    (Or.inr ⟨_, _, Quotient.eq.mpr ·⟩)

namespace Point

lemma eq_zero_or_eq_some (P : W.Point) : P = 0 ∨ ∃ x y : F, P.point = ⟦![x, y, 1]⟧ := by
  simpa only [Point.ext_iff] using Jacobian.eq_zero_or_eq_some P.nonsingular

lemma toAffineAddEquiv_zero : toAffineAddEquiv W 0 = 0 :=
  toAffineLift_zero

lemma toAffineAddEquiv_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) :
    toAffineAddEquiv W (mk h) = .some ((nonsingular_some ..).mp h) :=
  toAffineLift_some h

lemma toAffineAddEquiv_symm_zero : (toAffineAddEquiv W).symm 0 = 0 :=
  rfl

lemma toAffineAddEquiv_symm_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) :
    (toAffineAddEquiv W).symm (.some <| (nonsingular_some ..).mp h) = mk h :=
  rfl

@[simps!]
noncomputable def toAffineEquivSubtype (p : W.Point → Prop) :
    {P : W.Point // p P} ≃ {P : W.toAffine.Point // p P.toJacobian} :=
  (toAffineAddEquiv W).subtypeEquiv fun P =>
    (congr_arg p ((toAffineAddEquiv W).left_inv P).symm).to_iff

lemma toAffineEquivSubtype_zero {p : W.Point → Prop} (p0 : p 0) :
    toAffineEquivSubtype p ⟨0, p0⟩ = ⟨0, p0⟩ :=
  Subtype.ext toAffineLift_zero

lemma toAffineEquivSubtype_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) {p : W.Point → Prop}
    (ph : p <| mk h) :
    toAffineEquivSubtype p ⟨mk h, ph⟩ = ⟨.some <| (nonsingular_some ..).mp h, ph⟩ :=
  Subtype.ext <| toAffineLift_some h

lemma toAffineEquivSubtype_symm_zero {p : W.Point → Prop} (p0 : p 0) :
    (toAffineEquivSubtype p).symm ⟨0, p0⟩ = ⟨0, p0⟩ :=
  rfl

lemma toAffineEquivSubtype_symm_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧)
    {p : W.Point → Prop} (ph : p <| mk h) :
    (toAffineEquivSubtype p).symm ⟨.some <| (nonsingular_some ..).mp h, ph⟩ = ⟨mk h, ph⟩ :=
  rfl

variable (W) in
@[simps!]
noncomputable def equivOptionSubtype {p : W.Point → Prop} (p0 : p 0) : {P : W.Point // p P} ≃
    Option {xy : F × F // ∃ h : W.NonsingularLift ⟦![xy.1, xy.2, 1]⟧, p <| mk h} :=
  ((toAffineEquivSubtype p).trans <| Affine.Point.equivOptionSubtype W p0).trans
    (Equiv.setCongr <| Set.ext fun _ => by simpa only [← nonsingular_some] using by rfl).optionCongr

lemma equivOptionSubtype_zero {p : W.Point → Prop} (p0 : p 0) :
    equivOptionSubtype W p0 ⟨0, p0⟩ = none := by
  rw [equivOptionSubtype_apply, toAffineEquivSubtype_zero]
  rfl

lemma equivOptionSubtype_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) {p : W.Point → Prop}
    (p0 : p 0) (ph : p <| mk h) : equivOptionSubtype W p0 ⟨mk h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ := by
  rw [equivOptionSubtype_apply, toAffineEquivSubtype_some]
  rfl

lemma equivOptionSubtype_symm_none {p : W.Point → Prop} (p0 : p 0) :
    (equivOptionSubtype W p0).symm none = ⟨0, p0⟩ :=
  rfl

lemma equivOptionSubtype_symm_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧)
    {p : W.Point → Prop} (p0 : p 0) (ph : p <| mk h) :
    (equivOptionSubtype W p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨mk h, ph⟩ :=
  rfl

variable (W) in
@[simps!]
noncomputable def equivOption : W.Point ≃ Option {xy : F × F // W.Nonsingular ![xy.1, xy.2, 1]} :=
  (Equiv.Set.univ W.Point).symm.trans <| (equivOptionSubtype W trivial).trans
    (Equiv.setCongr <| Set.ext fun _ => exists_iff_of_forall fun _ => trivial).optionCongr

lemma equivOption_zero : equivOption W 0 = none := by
  erw [equivOption_apply, toAffineEquivSubtype_zero]
  rfl

lemma equivOption_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) :
    equivOption W (mk h) = .some ⟨⟨x, y⟩, h⟩ := by
  erw [equivOption_apply, toAffineEquivSubtype_some]
  rfl

lemma equivOption_symm_none : (equivOption W).symm none = 0 :=
  rfl

lemma equivOption_symm_some {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) :
    (equivOption W).symm (.some ⟨⟨x, y⟩, h⟩) = mk h :=
  rfl

variable (W) in
noncomputable def zsmulKerEquivOption (n : ℤ) : (zsmulAddGroupHom n : W.Point →+ W.Point).ker ≃
    Option {xy : F × F | ∃ h : W.NonsingularLift ⟦![xy.1, xy.2, 1]⟧, n • mk h = 0} :=
  equivOptionSubtype W <| smul_zero n

lemma zsmulKerEquivOption_zero (n : ℤ) : zsmulKerEquivOption W n 0 = none :=
  equivOptionSubtype_zero _

lemma zsmulKerEquivOption_some {n : ℤ} {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧)
    (hn : n • mk h = 0) : zsmulKerEquivOption W n ⟨mk h, hn⟩ = .some ⟨⟨x, y⟩, h, hn⟩ :=
  equivOptionSubtype_some ..

lemma zsmulKerEquivOption_symm_zero (n : ℤ) : (zsmulKerEquivOption W n).symm none = 0 :=
  rfl

lemma zsmulKerEquivOption_symm_some {n : ℤ} {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧)
    (hn : n • mk h = 0) : (zsmulKerEquivOption W n).symm (.some ⟨⟨x, y⟩, h, hn⟩) = ⟨mk h, hn⟩ :=
  rfl

lemma nonsingular_zsmul (n : ℤ) (P : W.Point) : W.NonsingularLift (n • P).point := by
  induction n using Int.negInduction with
  | nat n => induction n with
    | zero => simp [zero_point, nonsingularLift_zero]
    | succ _ h => simp only [Nat.cast_add, Nat.cast_one, _root_.add_smul, one_smul, add_point,
      nonsingularLift_addMap h P.nonsingular]
  | neg _ h => simp only [_root_.neg_smul, neg_point, nonsingularLift_negMap h]

theorem zsmul (n : ℤ) {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) :
    (n • mk h).point = ⟦evalEval x y ∘ ![W.φ n, W.ω n, W.ψ n]⟧ := by
  sorry

lemma zsmul_eq_zero_iff (n : ℤ) {x y : F} (h : W.NonsingularLift ⟦![x, y, 1]⟧) :
    n • mk h = 0 ↔ (W.ψ n).evalEval x y = 0 := by
  rw [Point.ext_iff, zsmul, zero_point, Quotient.eq]
  exact equiv_zero_iff_Z_eq_zero <| zsmul n h ▸ nonsingular_zsmul n (mk h)

noncomputable def optionOfZSMulKer {n : ℤ} (P : (zsmulAddGroupHom n : W.Point →+ W.Point).ker) :
    Option {xy : F × F | (W.ψ n).evalEval xy.1 xy.2 = 0} :=
  (zsmulKerEquivOption W n P).map fun xy =>
    by exact ⟨xy, (zsmul_eq_zero_iff n xy.property.choose).mp xy.property.choose_spec⟩

lemma optionOfZSMulKer_injective (n : ℤ) : (@optionOfZSMulKer _ _ W n).Injective :=
  (Option.map_injective <| by rintro ⟨_, _⟩ ⟨_, _⟩; simp only [Subtype.mk.injEq, imp_self]).comp
    (zsmulKerEquivOption W n).injective

instance (n : ℤ) : Fintype {xy : F × F | (W.ψ n).evalEval xy.1 xy.2 = 0} := by
  sorry

noncomputable instance (n : ℤ) : Fintype (zsmulAddGroupHom n : W.Point →+ W.Point).ker :=
  Fintype.ofInjective optionOfZSMulKer <| optionOfZSMulKer_injective n

end Point

end Jacobian

end WeierstrassCurve
