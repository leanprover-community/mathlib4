/-
Copyright (c) 2024 David Kurniadi Angdinata All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Michael Stoll, Junyan Xu
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Schemes associated to Weierstrass curves

This file defines the affine and projective schemes associated to a Weierstrass curve.
-/

universe u v w

/-! ## `Algebra.Polynomial.Bivariate` -/

namespace Polynomial

variable {R : Type u} {A : Type v} {B : Type w}

def aevalAeval [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A) : R[X][Y] →ₐ[R] A :=
  .mk (eval₂RingHom (aeval x).toRingHom y) fun r => by simp

variable (R A) in
@[simps]
noncomputable def algHomPolynomial₂Equiv [CommSemiring R] [CommSemiring A] [Algebra R A] :
    (R[X][Y] →ₐ[R] A) ≃ A × A where
  toFun f := (f (C X), f Y)
  invFun xy := aevalAeval xy.1 xy.2
  left_inv f := by ext <;> simp [aevalAeval]
  right_inv xy := by simp [aevalAeval]

@[simps]
def _root_.quotientIdealSpanSingletonAlgHomEquiv [CommSemiring R] [CommRing A] [Algebra R A]
    [CommSemiring B] [Algebra R B] (a : A) :
    (A ⧸ Ideal.span {a} →ₐ[R] B) ≃ {f : A →ₐ[R] B // f a = 0} where
  toFun f := ⟨f.comp (Ideal.Quotient.mkₐ _ _), by simp⟩
  invFun f := Ideal.Quotient.liftₐ _ f fun x hx ↦ by
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, f.2, mul_zero]
  left_inv f := by ext ⟨_⟩; simp
  right_inv f := by ext; simp

@[simps!]
noncomputable def _root_.adjoinRootAlgHomEquiv [CommRing R] [CommSemiring A] [Algebra R A]
    (p : R[X][Y]) : (AdjoinRoot p →ₐ[R] A) ≃ {xy : A × A // aevalAeval xy.1 xy.2 p = 0} :=
  (quotientIdealSpanSingletonAlgHomEquiv p).trans <|
    ((algHomPolynomial₂Equiv R A).image _).trans <|
    Equiv.setCongr <| by rw [Equiv.image_eq_preimage]; ext; simp; rfl

lemma evalEvalRingHom_comp_map_mapRingHom_algebraMap [CommSemiring R] [CommSemiring A] [Algebra R A]
    {x y : A} : (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom <| algebraMap R A) =
      (aevalAeval x y).toRingHom := by
  ext <;> simp [aevalAeval]

lemma evalEval_map_mapRingHom_algebraMap [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A)
    (p : R[X][Y]) : evalEval x y (p.map <| mapRingHom <| algebraMap R A) = aevalAeval x y p :=
  congr($evalEvalRingHom_comp_map_mapRingHom_algebraMap p)

end Polynomial

/-! ## `?` -/

section AlgHomEquiv

open AlgebraicGeometry CategoryTheory CommRingCat Opposite

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

def Algebra.mkOver : Over <| op <| of R :=
  .mk <| op <| ofHom <| algebraMap R A

def AlgHom.equivHomOver : (A →ₐ[R] B) ≃ (Algebra.mkOver R B ⟶ Algebra.mkOver R A) where
  toFun f := Over.homMk (op f.toRingHom) (unop_injective f.comp_algebraMap)
  invFun f := .mk f.left.unop fun r => congr(Quiver.Hom.unop $(Over.w f) r)
  left_inv f := by ext; simp
  right_inv f := by simp; rfl

variable {C : Type u} {D : Type v} [Category C] [Category D] (F : C ⥤ D)

@[simps!]
def CategoryTheory.Functor.mapOver (c : C) : Over c ⥤ Over (F.obj c) :=
  Comma.map (F₁ := F) (F₂ := 𝟭 _) (F := F) (𝟙 _) { app := fun _ ↦ 𝟙 _ }

@[simp]
lemma CategoryTheory.Functor.mapOver_hom (c : C) (c' : Over c) :
    ((F.mapOver c).obj c').hom = F.map c'.hom := by
  aesop_cat

noncomputable def Algebra.schemeSpec : Scheme :=
  Scheme.Spec.obj <| op <| of R

noncomputable def Algebra.schemeSpecOver : Over (Algebra.schemeSpec R) :=
  (Scheme.Spec.mapOver _).obj (Algebra.mkOver R A)

variable {F} in
def CategoryTheory.Functor.FullyFaithful.mapOver (ff : F.FullyFaithful) (c : C) :
    (F.mapOver c).FullyFaithful where
  preimage f := Over.homMk (ff.preimage f.left) (ff.map_injective <| by simpa using Over.w f)

noncomputable def AlgHom.equivSchemeOver :
    (A →ₐ[R] B) ≃ (Algebra.schemeSpecOver R B ⟶ Algebra.schemeSpecOver R A) :=
  (AlgHom.equivHomOver R A B).trans (Spec.fullyFaithful.mapOver _).homEquiv

end AlgHomEquiv

/-! ## `AlgebraicGeometry.EllipticCurve.Affine` -/

namespace WeierstrassCurve.Affine.Point

variable {R : Type u} [CommRing R] (W : Affine R)

@[simps]
def equivNonsingularSubtype {p : W.Point → Prop} (p0 : p 0) :
    {P : W.Point // p P} ≃ WithZero {xy : R × R // ∃ h : W.Nonsingular xy.1 xy.2, p <| some h} where
  toFun P := match P with
    | ⟨zero, _⟩ => none
    | ⟨@some _ _ _ x y h, ph⟩ => .some ⟨⟨x, y⟩, h, ph⟩
  invFun P := P.casesOn ⟨0, p0⟩ fun xy => ⟨some xy.property.choose, xy.property.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simps!]
def equivNonsingular : W.Point ≃ WithZero {xy : R × R // W.Nonsingular xy.1 xy.2} :=
  (Equiv.Set.univ W.Point).symm.trans <| (equivNonsingularSubtype W trivial).trans
    (Equiv.setCongr <| Set.ext fun _ => exists_iff_of_forall fun _ => trivial).optionCongr

end WeierstrassCurve.Affine.Point

namespace EllipticCurve.Affine

variable {R : Type u} [CommRing R] (E : EllipticCurve R)

noncomputable def equationEquivAlgHom (A : Type u) [CommRing A] [Algebra R A] :
    {xy : A × A // (E.baseChange A).toAffine.Equation xy.1 xy.2} ≃
      (E.toAffine.CoordinateRing →ₐ[R] A) :=
  ((adjoinRootAlgHomEquiv _).trans <| Equiv.setCongr <| by simp only [map_toWeierstrassCurve,
    WeierstrassCurve.Affine.map_polynomial, Polynomial.evalEval_map_mapRingHom_algebraMap]).symm

variable {E} in
lemma nonsingular' [Nontrivial R] {x y : R} (h : E.toAffine.Equation x y) :
    E.toAffine.Nonsingular x y :=
  E.toAffine.nonsingular_of_Δ_ne_zero h <| E.coe_Δ' ▸ E.Δ'.ne_zero

namespace Point

variable {E} in
def mk' [Nontrivial R] {x y : R} (h : E.toAffine.Equation x y) : E.toAffine.Point :=
  .some <| nonsingular' h

@[simps!]
def equivEquationSubtype [Nontrivial R] {p : E.toAffine.Point → Prop} (p0 : p 0) :
    {P : E.toAffine.Point // p P} ≃
      WithZero {xy : R × R // ∃ h : E.toAffine.Equation xy.1 xy.2, p <| mk' h} :=
  (WeierstrassCurve.Affine.Point.equivNonsingularSubtype E.toAffine p0).trans
    (Equiv.setCongr <| Set.ext fun _ => by exact ⟨fun h => ⟨h.choose.left, h.choose_spec⟩,
      fun h => ⟨nonsingular' h.choose, h.choose_spec⟩⟩).optionCongr

@[simps!]
def equivEquation [Nontrivial R] :
    E.toAffine.Point ≃ WithZero {xy : R × R // E.toAffine.Equation xy.1 xy.2} :=
  (WeierstrassCurve.Affine.Point.equivNonsingular E.toAffine).trans
    (Equiv.setCongr <| Set.ext fun _ => ⟨And.left, nonsingular'⟩).optionCongr

noncomputable def equivAlgHom (A : Type u) [Nontrivial A] [CommRing A] [Algebra R A] :
    (E.baseChange A).toAffine.Point ≃ WithZero (E.toAffine.CoordinateRing →ₐ[R] A) :=
  (equivEquation <| E.baseChange A).trans (equationEquivAlgHom E A).optionCongr

end Point

end EllipticCurve.Affine

/-! ## `AlgebraicGeometry.EllipticCurve.Projective` -/

namespace WeierstrassCurve.Projective

open MvPolynomial

variable {R : Type u} [CommRing R] (W : Projective R)

lemma isHomogeneous_polynomial : W.polynomial.IsHomogeneous 3 := by
  rw [← mem_homogeneousSubmodule]
  refine sub_mem (add_mem (add_mem ?_ ?_) ?_) (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_)
  · exact (isHomogeneous_X_pow ..).mul <| isHomogeneous_X ..
  · exact ((isHomogeneous_C_mul_X ..).mul <| isHomogeneous_X ..).mul <| isHomogeneous_X ..
  · exact (isHomogeneous_C_mul_X ..).mul <| isHomogeneous_X_pow ..
  · exact isHomogeneous_X_pow ..
  · exact (isHomogeneous_C_mul_X_pow ..).mul <| isHomogeneous_X ..
  · exact (isHomogeneous_C_mul_X ..).mul <| isHomogeneous_X_pow ..
  · exact isHomogeneous_C_mul_X_pow ..

instance : GradedRing <| homogeneousSubmodule (Fin 3) R where

  sorry -- `MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcommSemiring`?

lemma isHomogeneous_span_polynomial :
    (Ideal.span {W.polynomial}).IsHomogeneous <| homogeneousSubmodule (Fin 3) R :=
  Ideal.homogeneous_span (homogeneousSubmodule (Fin 3) R) {W.polynomial} <|
    by simpa only [Set.mem_singleton_iff, forall_eq] using ⟨3, W.isHomogeneous_polynomial⟩

abbrev CoordinateRing : Type u :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span {W.polynomial}

def quotientGrading (n : ℕ) : Submodule R W.CoordinateRing :=
  sorry -- `zjj/graded_and_fg/RingTheory/GradedAlgebra/Subgrading.lean` has `AddSubgroup`

instance : GradedAlgebra W.quotientGrading :=
  sorry -- ?

end WeierstrassCurve.Projective

/-! ## `AlgebraicGeometry.EllipticCurve.Scheme` -/

namespace WeierstrassCurve.Affine

/-! ## The affine scheme -/

open AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] (W : Affine R) (A : Type u) [CommRing A] [Algebra R A]

/-- The scheme `Spec R[W]`. -/
noncomputable def scheme : Scheme :=
  Algebra.schemeSpec W.CoordinateRing

/-- For an `R`-algebra `A`, the type of `A`-rational points of `Spec R[W]`. In other words, the type
of morphisms of schemes from `Spec A` to `Spec R[W]`. -/
def SchemePoint : Type u :=
  Algebra.schemeSpec A ⟶ W.scheme

/-- The scheme `Spec R[W]` over `Spec R`. -/
noncomputable def schemeOver : Over <| Algebra.schemeSpec R :=
  Algebra.schemeSpecOver R W.CoordinateRing

/-- For an `R`-algebra `A`, the type of `A`-rational points over `Spec R` of `Spec R[W]`. In other
words, the type of morphisms of schemes over `Spec R` from `Spec A` to `Spec R[W]`. -/
def SchemePointOver : Type u :=
  Algebra.schemeSpecOver R A ⟶ W.schemeOver

/-- The equivalence between the type of rational points of an elliptic curve `E` over `R` base
changed to `A` and the type of morphisms of schemes over `Spec R` from `Spec A` to `Spec R[E]`. -/
noncomputable def Point.equivSchemeOver [Nontrivial A] (E : EllipticCurve R) :
    (E.baseChange A).toAffine.Point ≃ WithZero (E.toAffine.SchemePointOver A) :=
  (EllipticCurve.Affine.Point.equivAlgHom E A).trans
    (AlgHom.equivSchemeOver R E.toAffine.CoordinateRing A).optionCongr

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Projective

/-! ## The projective scheme -/

open AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] (W : Projective R) (A : Type u) [CommRing A] [Algebra R A]

/-- The scheme `Proj R[W]`. -/
noncomputable def scheme : Scheme :=
  Proj W.quotientGrading

/-- For an `R`-algebra `A`, the type of `A`-rational points of `Proj R[W]`. In other words, the type
of morphisms of schemes from `Spec A` to `Proj R[W]`. -/
def SchemePoint : Type u :=
  Algebra.schemeSpec A ⟶ W.scheme

/-- The scheme `Proj R[W]` over `Spec R`. -/
noncomputable def schemeOver (W : Projective R) : Over <| Algebra.schemeSpec R :=
  sorry -- need structure morphism `Proj R[W] → Spec R`

/-- For an `R`-algebra `A`, the type of `A`-rational points over `Spec R` of `Proj R[W]`. In other
words, the type of morphisms of schemes over `Spec R` from `Spec A` to `Proj R[W]`. -/
def SchemePointOver : Type u :=
  Algebra.schemeSpecOver R A ⟶ W.schemeOver

/- TODO: The equivalence between the type of rational points of an elliptic curve `E` over `R` base
changed to `A` and the type of morphisms of schemes over `Spec R` from `Spec A` to `Spec R[E]`. -/

end WeierstrassCurve.Projective

section

open AlgebraicGeometry CategoryTheory


section

variable {R A} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)

noncomputable
def Proj.basicOpenImm  :
    Spec (.of <| HomogeneousLocalization.Away 𝒜 f) ⟶ Proj 𝒜 :=
    (projIsoSpec 𝒜 f f_deg hm).inv ≫ Scheme.ιOpens _

instance : IsOpenImmersion (Proj.basicOpenImm 𝒜 f f_deg hm) := by
  delta Proj.basicOpenImm; infer_instance

lemma Proj.opensRange_basicOpenImm :
    (Proj.basicOpenImm 𝒜 f f_deg hm).opensRange = ProjectiveSpectrum.basicOpen 𝒜 f := by
  ext1
  delta Proj.basicOpenImm
  simp only [Scheme.Hom.opensRange_coe, Scheme.comp_coeBase, Scheme.ofRestrict_val_base,
    TopCat.coe_comp, Set.range_comp]
  erw [(TopCat.homeoOfIso <| LocallyRingedSpace.forgetToTop.mapIso (projIsoSpec 𝒜 f f_deg hm).symm).range_eq_univ]
  rw [Set.image_univ]
  exact Subtype.range_val

def HomogeneousLocalization.algalg : R →+* (HomogeneousLocalization.Away 𝒜 f) where
  toFun r := .mk ⟨0, r • ⟨1, SetLike.GradedOne.one_mem⟩, ⟨1, SetLike.GradedOne.one_mem⟩, one_mem _⟩
  map_one' := by simp only [one_smul]; rfl
  map_mul' x y := by simp only [SetLike.mk_smul_mk, ← mk_mul]; congr <;> simp [mul_smul, smul_comm x y]
  map_add' x y := by simp only [SetLike.mk_smul_mk, ← mk_add]; congr <;> simp [add_smul, add_comm]
  map_zero' := by simp only [zero_smul]; rfl

instance : Algebra R (HomogeneousLocalization.Away 𝒜 f) := (HomogeneousLocalization.algalg 𝒜 f).toAlgebra

@[simp]
lemma HomogeneousLocalization.algebraMap_eq (r : R) :
  algebraMap R (Away 𝒜 f) r = .mk ⟨0, r • ⟨1, SetLike.GradedOne.one_mem⟩, ⟨1, SetLike.GradedOne.one_mem⟩, one_mem _⟩ := rfl

end

variable {R : Type u} [CommRing R] (W : WeierstrassCurve.Projective R) (A : Type u) [CommRing A] [Algebra R A]

#check AlgebraicGeometry.projIsoSpec


open MvPolynomial

noncomputable section

def WeierstrassCurve.Projective.P1l : MvPolynomial (Fin 3) R :=
  X 2 ^ 2 + (C W.a₁ * X 0 + C W.a₃) * X 2 - X 0 ^ 3 - C W.a₂ * X 0 ^ 2 - C W.a₄ * X 0 - C W.a₆

def WeierstrassCurve.Projective.P1r : MvPolynomial (Fin 3) R :=
  X 1 * (C W.a₁ * X 2 - (C 3 * X 0 ^ 2 + C (2 * W.a₂) * X 0 + C W.a₄)) - C 1

lemma WeierstrassCurve.Projective.mk_deg {x : MvPolynomial (Fin 3) R} {n} (hx : x.IsHomogeneous n) :
  Ideal.Quotient.mk _ x ∈ W.quotientGrading n := sorry

theorem WeierstrassCurve.Projective.polynomialX_deg : W.polynomialX.IsHomogeneous 2 := by
  rw [W.polynomialX_eq]
  apply IsHomogeneous.sub
  apply MvPolynomial.IsHomogeneous.mul (m := 1) (n := 1)
  apply MvPolynomial.IsHomogeneous.mul (m := 0) (n := 1)
  exact isHomogeneous_C (Fin 3) W.a₁
  exact isHomogeneous_X R 1
  exact isHomogeneous_X R 2
  apply IsHomogeneous.add

open HomogeneousLocalization (Away)
open Ideal
open SetLike

def a3inj : homogeneousSubmodule (Fin 3) R 3 →ₗ[R] Away W.quotientGrading (Ideal.Quotient.mk _ (W.polynomialX * X 2)) where
  toFun x := .mk ⟨3, ⟨_, W.mk_deg x.2⟩,
          ⟨_, W.mk_deg (W.polynomialX_deg.mul (isHomogeneous_X R 2))⟩, Submonoid.mem_powers _⟩
  map_add' x y := by
    ext1
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add, Fin.isValue,
      _root_.map_mul, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_add, ← Localization.add_mk_self]
  map_smul' x y := by
    ext1
    simp only [SetLike.val_smul, Algebra.smul_def, algebraMap_eq, _root_.map_mul, Fin.isValue,
      HomogeneousLocalization.val_mk, RingHom.id_apply,
      HomogeneousLocalization.algebraMap_eq, mk_smul_mk, mul_one, HomogeneousLocalization.val_mul,
      Localization.mk_mul]
    simp only [Fin.isValue, Submonoid.mk_mul_mk, one_mul]
    rfl

noncomputable
def to0 : MvPolynomial (Fin 3) R →+*
    (Away W.quotientGrading (Ideal.Quotient.mk _ (W.polynomialX * X 2))) :=
  (MvPolynomial.aeval
    ![a3inj W ⟨_, W.polynomialX_deg.mul (isHomogeneous_X R 0)⟩,
      a3inj W ⟨_, ((isHomogeneous_X R 2).pow 3)⟩,
      a3inj W ⟨_, (W.polynomialX_deg.mul (isHomogeneous_X R 1))⟩]).toRingHom

open HomogeneousLocalization

notation3 "mk" W => (Ideal.Quotient.mk (span {WeierstrassCurve.Projective.polynomial W}))

lemma Localization.eq_zero_of_eq {M} [CommMonoidWithZero M] {S : Submonoid M} (x : M) (s : S) (h : x = 0) :
  Localization.mk x s = 0 := by { subst h; exact mk_zero _ }

lemma to0P1l : to0 W W.P1l = 0 := by
  ext
  simp only [to0, Nat.succ_eq_add_one, Nat.reduceAdd, a3inj, Fin.isValue, _root_.map_mul,
    LinearMap.coe_mk, AddHom.coe_mk, map_pow, AlgHom.toRingHom_eq_coe,
    WeierstrassCurve.Projective.P1l, map_add, map_sub, RingHom.coe_coe, aeval_X,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, algHom_C,
    HomogeneousLocalization.algebraMap_eq, mk_smul_mk, Matrix.cons_val_zero, val_add, val_sub,
    val_pow, val_mk, val_mul, val_zero, Localization.mk_pow, Localization.add_mk, Localization.sub_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.eq_zero_of_eq
  simp only [Fin.isValue, SubmonoidClass.mk_pow, Submonoid.mk_mul_mk, one_mul, mul_one,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  simp only [← Quotient.mk_comp_algebraMap, RingHom.comp_apply,
    Algebra.smul_def, Fin.isValue, ← _root_.map_mul, ← map_pow, ← map_add, ← map_sub,
    MvPolynomial.algebraMap_eq, Fin.isValue, ← pow_two, ← pow_add, ← pow_mul,
    ← pow_succ, ← pow_succ']
  rw [Ideal.Quotient.eq_zero_iff_dvd]
  simp only [Fin.isValue, Nat.reducePow, Nat.reduceAdd, WeierstrassCurve.Projective.polynomial]
  use W.polynomialX ^ 10 * X 2 ^ 7
  rw [← sub_eq_zero]
  ring

lemma to0P1r : to0 W W.P1r = 0 := by
  ext
  simp only [to0, Nat.succ_eq_add_one, Nat.reduceAdd, a3inj, Fin.isValue, _root_.map_mul,
    LinearMap.coe_mk, AddHom.coe_mk, map_pow, AlgHom.toRingHom_eq_coe,
    WeierstrassCurve.Projective.P1r, map_add, map_sub, RingHom.coe_coe, aeval_X,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, algHom_C,
    HomogeneousLocalization.algebraMap_eq, mk_smul_mk, Matrix.cons_val_zero, val_add, val_sub,
    val_pow, val_mk, val_mul, val_zero, Localization.mk_pow, Localization.add_mk, Localization.sub_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, val_mk,
    SubmonoidClass.mk_pow, Submonoid.mk_mul_mk, one_mul, mul_one,
    Algebra.smul_mul_assoc, Algebra.mul_smul_comm, one_smul, Submonoid.LocalizationMap.mk'_self]
  apply Localization.eq_zero_of_eq
  simp only [Fin.isValue, ← map_pow, ← _root_.map_mul, ← pow_succ, Algebra.smul_def, ←
    Quotient.mk_comp_algebraMap, MvPolynomial.algebraMap_eq, RingHom.comp_apply, ← map_add, ←
    map_sub, ← pow_succ']
  rw [Ideal.Quotient.eq_zero_iff_dvd]
  convert_to _ ∣ (-(X 2 ^ 5 * X 0 ^ 2 * C 3) - X 2 ^ 5 * W.polynomialX +
      X 2 ^ 6 * C W.a₁ * X 1 +
    (-(X 2 ^ 6 * C W.a₂ * C 2 * X 0) - X 2 ^ 7 * C W.a₄)) * W.polynomialX ^ 4
  · simp only [Fin.isValue, Nat.reducePow, Nat.reduceAdd, mul_pow]
    ring
  apply dvd_mul_of_dvd_left
  use 0
  simp only [WeierstrassCurve.Projective.polynomial, Fin.isValue, map_ofNat,
    WeierstrassCurve.Projective.polynomialX_eq, _root_.map_mul]
  ring

noncomputable
def to01 : MvPolynomial (Fin 3) R ⧸ span {W.P1l, W.P1r} →+*
    (Away W.quotientGrading (Ideal.Quotient.mk _ (W.polynomialX * X 2))) := by
  apply Ideal.Quotient.lift (f := to0 W)
  show span {W.P1l, W.P1r} ≤ RingHom.ker (to0 W)
  rw [Ideal.span_le]
  rintro _ (rfl | rfl)
  · exact to0P1l W
  · exact to0P1r W

def toinv' : MvPolynomial (Fin 3) R ⧸ span {W.polynomial} →+*
    MvPolynomial (Fin 3) R ⧸ span {W.P1l, W.P1r} := by
  apply Ideal.Quotient.lift (f := (Ideal.Quotient.mk _).comp
    (MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 2, 1]).toRingHom)
  show span {W.polynomial} ≤ RingHom.ker _
  rw [Ideal.span_le]
  rintro _ rfl
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, AlgHom.toRingHom_eq_coe, mem_coe,
    RingHom.mem_ker]
  simp only [Fin.isValue, WeierstrassCurve.Projective.polynomial, map_sub, map_add, _root_.map_mul,
    map_pow, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, aeval_X, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
    map_one, mul_one, algHom_C, MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, one_pow]
  simp only [← map_sub, ← map_add, ← _root_.map_mul, ← map_pow]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine (show span {W.P1l} ≤ span {W.P1l, W.P1r} from span_mono (by simp)) ?_
  rw [Ideal.mem_span_singleton, WeierstrassCurve.Projective.P1l]
  use 1
  ring_nf

noncomputable
def to01inv : (Away W.quotientGrading (Ideal.Quotient.mk _ (W.polynomialX * X 2))) →+*
    MvPolynomial (Fin 3) R ⧸ span {W.P1l, W.P1r} := by
  refine RingHom.comp (?_) (algebraMap _ (Localization.Away ((mk W) (W.polynomialX * X 2))))
  apply IsLocalization.Away.lift ((mk W) (W.polynomialX * X 2)) (g := toinv' W)
  apply isUnit_of_mul_eq_one (b := Ideal.Quotient.mk _ (.X 1))
  simp only [toinv', Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, AlgHom.toRingHom_eq_coe,
    WeierstrassCurve.Projective.polynomialX_eq, map_ofNat, _root_.map_mul, map_sub, map_add,
    map_pow, Ideal.Quotient.lift_mk, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    algHom_C, MvPolynomial.algebraMap_eq, aeval_X, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, map_one, mul_one, Matrix.cons_val_zero, one_pow]
  rw [(show (3 : MvPolynomial (Fin 3) R ⧸ span {W.P1l, W.P1r}) = 1 + 2 from rfl)]
  simp only [two_mul, ← map_sub, ← map_add, ← _root_.map_mul, ← map_pow, add_mul, one_mul]
  rw [← sub_eq_zero, ← (Ideal.Quotient.mk (span {W.P1l, W.P1r})).map_one, ← map_sub]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simp only [map_add]
  refine (show span {W.P1r} ≤ span {W.P1l, W.P1r} from span_mono (by simp)) ?_
  rw [Ideal.mem_span_singleton, WeierstrassCurve.Projective.P1r]
  use 1
  simp only [Fin.isValue, map_ofNat, _root_.map_mul, map_one, mul_one, sub_left_inj]
  ring_nf

def to01_inv (f : MvPolynomial (Fin 3) R) (n : ℕ) : MvPolynomial (Fin 3) R :=
  MvPolynomial.aeval ![.X 0, .X 2, 1] f * (.X 2) ^ n


lemma to01Prop : Function.Bijective (to01 W) := sorry

def Cover1 : Spec (.of (MvPolynomial (Fin 3) R ⧸ span {W.P1l, W.P1r})) ⟶ W.scheme :=
  (Scheme.Spec.mapIso (RingEquiv.ofBijective (to01 W) (to01Prop W)).toCommRingCatIso.op).inv ≫
    Proj.basicOpenImm W.quotientGrading (Ideal.Quotient.mk _ (W.polynomialX * MvPolynomial.X 2)) (m := 3)
      (W.mk_deg (W.polynomialX_deg.mul (isHomogeneous_X R 2)))
    zero_lt_three


instance : IsOpenImmersion (Cover1 W) := by { delta Cover1; infer_instance }

example :
    (Cover1 W).opensRange = ProjectiveSpectrum.basicOpen W.quotientGrading ((mk W) <| W.polynomialX * MvPolynomial.X 2) := by
  ext1
  delta Cover1
  simp only [Scheme.Hom.opensRange_coe, Scheme.comp_coeBase, Scheme.ofRestrict_val_base,
    TopCat.coe_comp, Set.range_comp]
  erw [(TopCat.homeoOfIso <| Scheme.forgetToTop.mapIso (Scheme.Spec.mapIso (RingEquiv.ofBijective (to01 W) (to01Prop W)).toCommRingCatIso.op).symm).range_eq_univ]
  rw [Set.image_univ]
  exact congr_arg (fun x ↦ x.1 : TopologicalSpace.Opens _ → Set _) (Proj.opensRange_basicOpenImm W.quotientGrading (Ideal.Quotient.mk _ (W.polynomialX * MvPolynomial.X 2)) (m := 3)
      (W.mk_deg (W.polynomialX_deg.mul (isHomogeneous_X R 2))) zero_lt_three)

end
