/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patricio Gallardo Candela, Johan Commelin, Yun Liu, Sophie Morel, David Swinarski,
Weihong Xu
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!

# Lemmas for the Grassmannian scheme

This is a collection of lemmas that are used in the formalization of the Grassmannian schemes.
They should be included in various other files.

# Notes.

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry" in
June 2024.
-/

open AlgebraicGeometry Scheme FiniteDimensional CategoryTheory Matrix

noncomputable section

universe u v w

section

/-- If we give ourselves a scheme gluing data `GD`, and if we have morphisms from the charts
`GD.U i` of the gluing data to a scheme `Y` that are compatible with the transition morphisms
between charts, then we get a morphism from the glued scheme `GD.glued` to `Y`. This is an easy
consequence of the definition of `GD.glued` as a `Multicoequalized`, but is included here for
convenience.-/
def AlgebraicGeometry.Scheme.GlueData.glueMorphisms (GD : Scheme.GlueData)
    {Y : Scheme} (f : (i : GD.J) → GD.U i ⟶ Y) (hf : ∀ (i j : GD.J),
    GD.f i j ≫ (f i) = GD.t i j ≫ GD.f j i ≫ (f j)) :
    GD.glued ⟶ Y := by
  refine Limits.Multicoequalizer.desc _ Y f ?_
  simp only [GlueData.diagram_l, GlueData.diagram_left, GlueData.diagram_right, Prod.forall,
    GlueData.diagram_fstFrom, GlueData.diagram_fst, GlueData.diagram_sndFrom, GlueData.diagram_snd,
    Category.assoc]
  exact hf

@[simp, reassoc]
theorem AlgebraicGeometry.Scheme.GlueData.ι_glueMorphisms (GD : Scheme.GlueData) {Y : Scheme}
    (f : (i : GD.J) → GD.U i ⟶ Y) (hf : ∀ (i j : GD.J), GD.f i j ≫ (f i) =
    GD.t i j ≫ GD.f j i ≫ (f j)) (i : GD.J) : GD.ι i ≫ GD.glueMorphisms f hf = f i := by
  erw [Limits.Multicoequalizer.π_desc]

theorem AlgebraicGeometry.Scheme.GlueData.hom_ext (GD : Scheme.GlueData) {Y : Scheme}
    (f₁ f₂ : GD.glued ⟶ Y) (h : ∀ (i : GD.J), GD.ι i ≫ f₁ = GD.ι i ≫ f₂) : f₁ = f₂ :=
  GD.openCover.hom_ext f₁ f₂ h

end

section

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

lemma Algebra.TensorProduct.algebraMap : algebraMap R (TensorProduct R A B) =
    Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap R A) := by
  ext _
  simp only [algebraMap_apply, RingHom.coe_comp, Function.comp_apply, includeLeftRingHom_apply]

end

section

variable {m n o α β : Type*} [Fintype n]
  [NonAssocSemiring α] [NonAssocSemiring β] (M : Matrix m n α) (N : Matrix n o α) (f : α →+* β)

theorem RingHom.map_matrix_mul' :
    (M * N).map f = (M.map f.toFun) * (N.map f.toFun) := by
  ext i j
  simp only [map_apply, map_matrix_mul, toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe]

end

section
variable {m α β : Type*} [Fintype m] [DecidableEq m]
  [Ring α] [Ring β] (M : Matrix m m α) (f : α →+* β)

theorem RingHom.map_inv (x : α) (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  change f (Ring.inverse (IsUnit.unit hx).1) = _
  rw [Ring.inverse_unit]; erw [← Units.coe_map_inv]; rw [← Ring.inverse_unit, Units.coe_map]
  rfl

end

section

lemma AlgHom.map_inv {R : Type*} {α : Type*} {β : Type*} [CommRing R] [Ring α] [Ring β]
    [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) (x : α) (hx : IsUnit x) :
    f (Ring.inverse x) = Ring.inverse (f x) := by
  erw [RingHom.map_inv _ _ hx]; rfl

end

namespace Matrix

variable {m n m₁ m₂ α : Type*} (e₁ : m₁ → m) (e₂ : m₂ → m)
  (M : Matrix m n α) (N : Matrix m n α)

lemma eq_of_submatrix_eq (h₁ : M.submatrix e₁ id = N.submatrix e₁ id)
    (h₂ : M.submatrix e₂ id = N.submatrix e₂ id) (hsurj : ∀ (x : m),
  (∃ (y : m₁), e₁ y = x) ∨ (∃ (y : m₂), e₂ y = x)) :
    M = N := by
  apply Matrix.ext; intro p q
  cases (hsurj p) with
  | inl h =>
    obtain ⟨p', h⟩ := h
    rw [← h]
    conv_lhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply M e₁ id]
    conv_rhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply N e₁ id]
    rw [h₁]
  | inr h =>
    obtain ⟨p', h⟩ := h
    rw [← h]
    conv_lhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply M e₂ id]
    conv_rhs => congr; rfl; change id q
    rw [← Matrix.submatrix_apply N e₂ id]
    rw [h₂]

end Matrix

section

variable (R : Type*) [CommRing R] (f : R)

lemma Localization.Away.map_unit : IsUnit (algebraMap R (Localization.Away f) f) := by
   refine isUnit_iff_exists_inv.mpr ?_
   existsi IsLocalization.Away.invSelf f
   simp only [IsLocalization.Away.mul_invSelf]

lemma IsLocalization.Away.invSelf_unit :
    IsUnit (IsLocalization.Away.invSelf (S := Localization.Away f) f) := by
   refine isUnit_iff_exists_inv.mpr ?_
   existsi algebraMap R (Localization.Away f) f
   rw [mul_comm]; simp only [mul_invSelf]

end

instance basic_open_isOpenImmersion' {R : Type*} [CommRing R] (f : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))) :=
  @basic_open_isOpenImmersion (CommRingCat.of R) _
