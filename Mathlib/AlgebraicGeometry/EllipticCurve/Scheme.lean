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

instance : GradedRing <| homogeneousSubmodule (Fin 3) R :=
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
