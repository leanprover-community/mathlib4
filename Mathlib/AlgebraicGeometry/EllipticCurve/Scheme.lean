/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
-/

variable (R A A') [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']

open CategoryTheory Opposite AlgebraicGeometry

/-- -/
def Algebra.mkOver : Over (op <| CommRingCat.of R) :=
  .mk (op <| CommRingCat.ofHom <| algebraMap R A)

/-- -/
def AlgHom.equivHomOver : (A →ₐ[R] A') ≃ (Algebra.mkOver R A' ⟶ Algebra.mkOver R A) where
  toFun f := Over.homMk (op f.toRingHom) (unop_injective f.comp_algebraMap)
  invFun f := .mk f.left.unop fun r ↦ congr(Quiver.Hom.unop $(Over.w f) r)
  left_inv f := by ext1; simp
  right_inv f := by simp; rfl

variable {C D} [Category C] [Category D] (F : C ⥤ D)
/-- -/
@[simps!] def CategoryTheory.Functor.mapOver (c : C) : Over c ⥤ Over (F.obj c) :=
  Comma.map (F₁ := F) (F₂ := 𝟭 _) (F := F) (𝟙 _) { app := fun _ ↦ 𝟙 _ }

@[simp] lemma CategoryTheory.Functor.mapOver_hom (c : C) (c' : Over c) :
    ((F.mapOver c).obj c').hom = F.map c'.hom := by simp

/-- -/
noncomputable def Algebra.schemeSpecOver : Over (Scheme.Spec.obj <| op <| CommRingCat.of R) :=
  (Scheme.Spec.mapOver _).obj (Algebra.mkOver R A)

variable {F} in
/-- -/
def CategoryTheory.Functor.FullyFaithful.mapOver (ff : F.FullyFaithful) (c : C) :
    (F.mapOver c).FullyFaithful where
  preimage f := Over.homMk (ff.preimage f.left) (ff.map_injective <| by simpa using Over.w f)

/-- -/
noncomputable def AlgHom.equivSchemeOver :
    (A →ₐ[R] A') ≃ (Algebra.schemeSpecOver R A' ⟶ Algebra.schemeSpecOver R A) :=
  (AlgHom.equivHomOver R A A').trans (Spec.fullyFaithful.mapOver _).homEquiv
