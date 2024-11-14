/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.CategoryTheory.Adjunction.Over

/-!
# Under `CommRingCat`

In this file we provide basic API for `Under R` when `R : CommRingCat`. `Under R` is
(equivalent to) the category of commutative `R`-algebras. For not necessarily commutative
algebras, use `AlgebraCat R` instead.
-/

noncomputable section

universe u

open TensorProduct CategoryTheory Limits

namespace CommRingCat

variable {R S : CommRingCat.{u}}

instance : CoeSort (Under R) (Type u) where
  coe A := A.right

instance (A : Under R) : Algebra R A := RingHom.toAlgebra A.hom

/-- Turn a morphism in `Under R` into an algebra homomorphism. -/
def toAlgHom {A B : Under R} (f : A ⟶ B) : A →ₐ[R] B where
  __ := f.right
  commutes' a := by
    have : (A.hom ≫ f.right) a = B.hom a := by simp
    simpa only [Functor.const_obj_obj, Functor.id_obj, CommRingCat.comp_apply] using this

@[simp]
lemma toAlgHom_id (A : Under R) : toAlgHom (𝟙 A) = AlgHom.id R A := rfl

@[simp]
lemma toAlgHom_comp {A B C : Under R} (f : A ⟶ B) (g : B ⟶ C) :
    toAlgHom (f ≫ g) = (toAlgHom g).comp (toAlgHom f) := rfl

@[simp]
lemma toAlgHom_apply {A B : Under R} (f : A ⟶ B) (a : A) :
    toAlgHom f a = f.right a :=
  rfl

variable (R) in
/-- -/
@[simps! hom, simps! (config := .lemmasOnly) right]
def mkUnder (A : Type u) [CommRing A] [Algebra R A] : Under R :=
  Under.mk (CommRingCat.ofHom <| algebraMap R A)

/-- Make a morphism in `Under R` from an algebra map. -/
def fromAlgHom {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : mkUnder R A ⟶ mkUnder R B :=
  Under.homMk f.toRingHom <| by
    ext a
    exact f.commutes' a

@[simp]
lemma fromAlgHom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (a : A) :
    (fromAlgHom f).right a = f a :=
  rfl

@[simp]
lemma fromAlgHom_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (fromAlgHom (g.comp f)) = fromAlgHom f ≫ fromAlgHom g :=
  rfl

lemma mkUnder_ext {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {f g : mkUnder R A ⟶ mkUnder R B} (h : ∀ a : A, f.right a = g.right a) :
    f = g := by
  ext x
  exact h x

/-- Make an isomorphism in `Under R` from an algebra isomorphism. -/
def fromAlgEquiv {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) :
    mkUnder R A ≅ mkUnder R B where
  hom := fromAlgHom f.toAlgHom
  inv := fromAlgHom f.symm.toAlgHom
  hom_inv_id := by
    ext (a : (mkUnder R A).right)
    simp
  inv_hom_id := by
    ext a
    simp

@[simp]
lemma fromAlgEquiv_hom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (a : A) :
    (fromAlgEquiv f).hom.right a = f a := rfl

@[simp]
lemma fromAlgEquiv_inv_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (b : B) :
    (fromAlgEquiv f).inv.right b = f.symm b := rfl

@[simp]
lemma fromAlgEquiv_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (fromAlgEquiv (f.trans g)) = fromAlgEquiv f ≪≫ fromAlgEquiv g :=
  rfl

variable [Algebra R S]

variable (R S) in
/-- The base change functor `A ↦ S ⊗[R] A`. -/
@[simps! map_right]
def tensorProd : Under R ⥤ Under S where
  obj A := mkUnder S (S ⊗[R] A)
  map f := fromAlgHom <| Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f)
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

variable (S) in
/-- The natural isomorphism `S ⊗[R] A ≅ pushout A.hom (algebraMap R S)` in `Under S`. -/
def tensorProdObjIsoPushoutObj (A : Under R) :
    mkUnder S (S ⊗[R] A) ≅ (Under.pushout (algebraMap R S)).obj A :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout <| by
    simp only [Functor.const_obj_obj, Under.pushout_obj, Functor.id_obj, Under.mk_right,
      mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom, Under.mk_hom]
    rfl

@[reassoc (attr := simp)]
lemma pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inl A.hom (algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

@[reassoc (attr := simp)]
lemma pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inr A.hom (algebraMap R S) ≫
      (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

/-- `A ↦ S ⊗[R] A` is naturally isomorphic to `A ↦ pushout A.hom (algebraMap R S)`. -/
def tensorProdIsoPushout : tensorProd R S ≅ Under.pushout (algebraMap R S) :=
  NatIso.ofComponents (fun A ↦ tensorProdObjIsoPushoutObj S A) <| by
    intro A B f
    dsimp
    rw [← cancel_epi (tensorProdObjIsoPushoutObj S A).inv]
    ext : 1
    apply pushout.hom_ext
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext x
      simp [mkUnder_right]
    · rw [← cancel_mono (tensorProdObjIsoPushoutObj S B).inv.right]
      ext (x : S)
      simp [mkUnder_right]

end CommRingCat
