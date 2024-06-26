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

namespace Polynomial -- `Algebra.Polynomial.Bivariate`

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

lemma evalEvalRingHom_comp_map_mapRingHom_algebraMap [CommRing R] [CommSemiring A] [Algebra R A]
    {x y : A} : (evalEvalRingHom x y).comp (mapRingHom <| mapRingHom <| algebraMap R A) =
      (aevalAeval x y).toRingHom := by
  ext <;> simp [aevalAeval]

lemma evalEval_map_mapRingHom_algebraMap [CommRing R] [CommSemiring A] [Algebra R A] (x y : A)
    (p : R[X][Y]) : evalEval x y (p.map <| mapRingHom <| algebraMap R A) = aevalAeval x y p :=
  congr($evalEvalRingHom_comp_map_mapRingHom_algebraMap p)

end Polynomial

section AlgHomEquiv -- `?`

open AlgebraicGeometry CategoryTheory CommRingCat Opposite

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

def Algebra.mkOver : Over <| op <| of R :=
  .mk <| op <| ofHom <| algebraMap R A

def AlgHom.equivHomOver : (A →ₐ[R] B) ≃ (Algebra.mkOver R B ⟶ Algebra.mkOver R A) where
  toFun f := Over.homMk (op f.toRingHom) (unop_injective f.comp_algebraMap)
  invFun f := .mk f.left.unop fun r => congr(Quiver.Hom.unop $(Over.w f) r)
  left_inv f := by ext; simp
  right_inv f := by simp; rfl

variable {C D} [Category C] [Category D] (F : C ⥤ D)

@[simps!] def CategoryTheory.Functor.mapOver (c : C) : Over c ⥤ Over (F.obj c) :=
  Comma.map (F₁ := F) (F₂ := 𝟭 _) (F := F) (𝟙 _) { app := fun _ ↦ 𝟙 _ }

@[simp] lemma CategoryTheory.Functor.mapOver_hom (c : C) (c' : Over c) :
    ((F.mapOver c).obj c').hom = F.map c'.hom := by aesop_cat

noncomputable def Algebra.schemeSpecOver : Over (Scheme.Spec.obj <| op <| CommRingCat.of R) :=
  (Scheme.Spec.mapOver _).obj (Algebra.mkOver R A)

variable {F} in
def CategoryTheory.Functor.FullyFaithful.mapOver (ff : F.FullyFaithful) (c : C) :
    (F.mapOver c).FullyFaithful where
  preimage f := Over.homMk (ff.preimage f.left) (ff.map_injective <| by simpa using Over.w f)

noncomputable def AlgHom.equivSchemeOver :
    (A →ₐ[R] B) ≃ (Algebra.schemeSpecOver R B ⟶ Algebra.schemeSpecOver R A) :=
  (AlgHom.equivHomOver R A B).trans (Spec.fullyFaithful.mapOver _).homEquiv

end AlgHomEquiv

namespace WeierstrassCurve.Affine

open AlgebraicGeometry CategoryTheory CommRingCat Polynomial

variable {R : Type u} [CommRing R] (W : Affine R) (A : Type u) [CommRing A] [Algebra R A]

namespace Point

def equivOptionSubtypeFun (p : W.Point → Prop) :
    {P : W.Point // p P} → Option {xy : R × R // ∃ h : W.Nonsingular xy.1 xy.2, p <| some h}
  | ⟨zero, _⟩ => none
  | ⟨@some _ _ _ x y h, ph⟩ => .some ⟨⟨x, y⟩, h, ph⟩

@[simps]
def equivOptionSubtype {p : W.Point → Prop} (p0 : p 0) :
    {P : W.Point // p P} ≃ Option {xy : R × R // ∃ h : W.Nonsingular xy.1 xy.2, p <| some h} where
  toFun := equivOptionSubtypeFun W p
  invFun P := P.casesOn ⟨0, p0⟩ fun xy => ⟨some xy.property.choose, xy.property.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simps!]
def equivOption : W.Point ≃ Option {xy : R × R // W.Nonsingular xy.1 xy.2} :=
  (Equiv.Set.univ W.Point).symm.trans <| (equivOptionSubtype W trivial).trans
    (Equiv.setCongr <| Set.ext fun _ => exists_iff_of_forall fun _ => trivial).optionCongr

end Point

/-- The affine scheme `Spec R[W]`. -/
noncomputable def scheme : Scheme :=
  Spec <| of W.CoordinateRing

namespace Scheme

/-- For an `R`-algebra `A`, the type of `A`-rational points of `Spec R[W]`. In other words, the type
of morphisms of affine schemes from `Spec A` to `Spec R[W]`. -/
def Point : Type u :=
  Spec (of A) ⟶ W.scheme

/-- The morphism of spectra `Spec R[W] → Spec R` induced by an algebra homomorphism `R →+* R[W]`. -/
noncomputable def map : (scheme W).Hom <| Spec <| of R :=
  Spec.map <| ofHom <| algebraMap R W.CoordinateRing

/-- For an `R`-algebra `A`, the type of `A`-rational points over `Spec R` of `Spec R[W]`. In other
words, the type of morphisms of affine schemes over `Spec R` from `Spec A` to `Spec R[W]`. -/
def PointOver : Type u :=
  Over.mk (Spec.map <| ofHom <| algebraMap R A) ⟶ Over.mk (map W)

variable (E : EllipticCurve R)

def equivOption [Nontrivial R] :
    E.toAffine.Point ≃
      Option {xy : R × R // E.toAffine.Equation xy.1 xy.2} :=
  (Point.equivOption E.toWeierstrassCurve).trans
    (Equiv.setCongr <| Set.ext fun _ => ⟨And.left, EllipticCurve.Affine.nonsingular E⟩).optionCongr

def aevalAevalEquiv (p : R[X][Y]) :
    {xy : A × A // aevalAeval xy.1 xy.2 p = 0} ≃
      {xy : A × A // evalEval xy.1 xy.2 (p.map <| mapRingHom <| algebraMap R A) = 0} :=
  Equiv.setCongr <| by simp only [evalEval_map_mapRingHom_algebraMap]

noncomputable def equiv [Nontrivial A] :
    (E.toAffine.CoordinateRing →ₐ[R] A) ≃
      {xy : A × A // (E.baseChange A).toAffine.Equation xy.1 xy.2} :=
  (adjoinRootAlgHomEquiv _).trans <| (aevalAevalEquiv ..).trans <| Equiv.setCongr <|
    Set.ext fun _ => by simp only [EllipticCurve.map_toWeierstrassCurve, map_polynomial]

noncomputable def equiv' [Nontrivial A] :
    Option (PointOver E.toWeierstrassCurve A) ≃ E.toWeierstrassCurve⟮A⟯ :=
  ((AlgHom.equivSchemeOver ..).symm.trans <| equiv ..).optionCongr.trans <|
    (equivOption <| E.baseChange A).symm

end Scheme

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Projective

open AlgebraicGeometry CategoryTheory CommRingCat MvPolynomial

variable {R : Type u} [CommRing R] (W : Projective R)

lemma isHomogenous_polynomial : W.polynomial.IsHomogeneous 3 := by
  rw [← mem_homogeneousSubmodule]
  refine sub_mem (add_mem (add_mem ?_ ?_) ?_) (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_)
  · exact (isHomogeneous_X_pow ..).mul <| isHomogeneous_X ..
  · exact ((isHomogeneous_C_mul_X ..).mul <| isHomogeneous_X ..).mul <| isHomogeneous_X ..
  · exact (isHomogeneous_C_mul_X ..).mul <| isHomogeneous_X_pow ..
  · exact isHomogeneous_X_pow ..
  · exact (isHomogeneous_C_mul_X_pow ..).mul <| isHomogeneous_X ..
  · exact (isHomogeneous_C_mul_X ..).mul <| isHomogeneous_X_pow ..
  · exact isHomogeneous_C_mul_X_pow ..

-- MvPolynomial.IsHomogeneous.HomogeneousSubmodule.gcommSemiring?
instance : GradedRing <| homogeneousSubmodule (Fin 3) R :=
  sorry

def I : Ideal <| MvPolynomial (Fin 3) R :=
  Ideal.span {W.polynomial}

lemma isHomogeneous_I : W.I.IsHomogeneous <| homogeneousSubmodule (Fin 3) R :=
  Ideal.homogeneous_span (homogeneousSubmodule (Fin 3) R) {W.polynomial} <|
    by simpa only [Set.mem_singleton_iff, forall_eq] using ⟨3, W.isHomogenous_polynomial⟩

abbrev CoordinateRing : Type u :=
  MvPolynomial (Fin 3) R ⧸ W.I

def quotientGrading (n : ℕ) : AddSubgroup (MvPolynomial (Fin 3) R ⧸ W.I) :=
  sorry

def quotientGrading' (n : ℕ) : Submodule R W.CoordinateRing where
  smul_mem' := sorry
  __ := W.quotientGrading n

instance : GradedAlgebra W.quotientGrading' :=
  sorry

noncomputable def scheme : Scheme :=
  Proj W.quotientGrading'

variable (A : Type u) [CommRing A] [Algebra R A]

/-- For an `R`-algebra `A`, the type of `A`-rational points of `Proj R[W]`. In other words, the type
of morphisms of affine schemes from `Spec A` to `Proj R[W]`. -/
def Point : Type u :=
  Spec (of A) ⟶ W.scheme

/-- The morphism of spectra `Proj R[W] → Spec R` induced by an algebra homomorphism `R →+* R[W]`. -/
noncomputable def map : (scheme W).Hom <| Spec <| of R :=
  sorry

/-- For an `R`-algebra `A`, the type of `A`-rational points over `Spec R` of `Proj R[W]`. In other
words, the type of morphisms of affine schemes over `Spec R` from `Spec A` to `Proj R[W]`. -/
def PointOver : Type u :=
  Over.mk (Spec.map <| ofHom <| algebraMap R A) ⟶ sorry

end WeierstrassCurve.Projective
