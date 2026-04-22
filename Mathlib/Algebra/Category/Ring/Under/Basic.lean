/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Under `CommRingCat`

In this file we provide basic API for `Under R` when `R : CommRingCat`. `Under R` is
(equivalent to) the category of commutative `R`-algebras. For not necessarily commutative
algebras, use `AlgCat R` instead.
-/

@[expose] public section

noncomputable section

universe u

open TensorProduct CategoryTheory Limits

variable {R S : CommRingCat.{u}}

namespace CommRingCat

instance : CoeSort (Under R) (Type u) where
  coe A := A.right

instance (A : Under R) : Algebra R A := RingHom.toAlgebra A.hom.hom

set_option backward.isDefEq.respectTransparency false in
/-- Turn a morphism in `Under R` into an algebra homomorphism. -/
def toAlgHom {A B : Under R} (f : A ⟶ B) : A →ₐ[R] B where
  __ := f.right.hom
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
/-- Make an object of `Under R` from an `R`-algebra. -/
@[simps! hom, simps! -isSimp right]
def mkUnder (A : Type u) [CommRing A] [Algebra R A] : Under R :=
  Under.mk (CommRingCat.ofHom <| algebraMap R A)

@[ext]
lemma mkUnder_ext {A : Type u} [CommRing A] [Algebra R A] {B : Under R}
    {f g : mkUnder R A ⟶ B} (h : ∀ a : A, f.right a = g.right a) :
    f = g := by
  ext x
  exact h x

end CommRingCat

namespace AlgHom

/-- Make a morphism in `Under R` from an algebra map. -/
def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : CommRingCat.mkUnder R A ⟶ CommRingCat.mkUnder R B :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) <| by
    ext a
    exact f.commutes' a

@[simp]
lemma toUnder_right {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (a : A) :
    f.toUnder.right a = f a :=
  rfl

@[simp]
lemma toUnder_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toUnder = f.toUnder ≫ g.toUnder :=
  rfl

end AlgHom

namespace AlgEquiv

/-- Make an isomorphism in `Under R` from an algebra isomorphism. -/
def toUnder {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) :
    CommRingCat.mkUnder R A ≅ CommRingCat.mkUnder R B where
  hom := f.toAlgHom.toUnder
  inv := f.symm.toAlgHom.toUnder
  hom_inv_id := by
    ext (a : (CommRingCat.mkUnder R A).right)
    simp
  inv_hom_id := by
    ext a
    simp

@[simp]
lemma toUnder_hom_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (a : A) :
    f.toUnder.hom.right a = f a := rfl

@[simp]
lemma toUnder_inv_right_apply {A B : Type u} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A ≃ₐ[R] B) (b : B) :
    f.toUnder.inv.right b = f.symm b := rfl

@[simp]
lemma toUnder_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (f.trans g).toUnder = f.toUnder ≪≫ g.toUnder :=
  rfl

end AlgEquiv

namespace CommRingCat

variable [Algebra R S]

variable (R S) in
/-- The base change functor `A ↦ S ⊗[R] A`. -/
@[simps! map_right]
def tensorProd : Under R ⥤ Under S where
  obj A := mkUnder S (S ⊗[R] A)
  map f := Algebra.TensorProduct.map (AlgHom.id S S) (toAlgHom f) |>.toUnder
  map_comp {X Y Z} f g := by simp [Algebra.TensorProduct.map_id_comp]

set_option backward.isDefEq.respectTransparency false in
variable (S) in
/-- The natural isomorphism `S ⊗[R] A ≅ pushout A.hom (algebraMap R S)` in `Under S`. -/
def tensorProdObjIsoPushoutObj (A : Under R) :
    mkUnder S (S ⊗[R] A) ≅ (Under.pushout (ofHom <| algebraMap R S)).obj A :=
  Under.isoMk (CommRingCat.isPushout_tensorProduct R S A).flip.isoPushout <| by
    simp only [Under.pushout_obj, Under.mk_right,
      mkUnder_hom, AlgHom.toRingHom_eq_coe, IsPushout.inr_isoPushout_hom, Under.mk_hom]
    rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pushout_inl_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inl A.hom (ofHom <| algebraMap R S) ≫ (tensorProdObjIsoPushoutObj S A).inv.right =
      (ofHom <| Algebra.TensorProduct.includeRight.toRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma pushout_inr_tensorProdObjIsoPushoutObj_inv_right (A : Under R) :
    pushout.inr A.hom (ofHom <| algebraMap R S) ≫
      (tensorProdObjIsoPushoutObj S A).inv.right =
      (CommRingCat.ofHom <| Algebra.TensorProduct.includeLeftRingHom) := by
  simp [tensorProdObjIsoPushoutObj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R S) in
/-- `A ↦ S ⊗[R] A` is naturally isomorphic to `A ↦ pushout A.hom (algebraMap R S)`. -/
def tensorProdIsoPushout : tensorProd R S ≅ Under.pushout (ofHom <| algebraMap R S) :=
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

@[simp]
lemma tensorProdIsoPushout_app (A : Under R) :
    (tensorProdIsoPushout R S).app A = tensorProdObjIsoPushoutObj S A :=
  rfl

end CommRingCat
