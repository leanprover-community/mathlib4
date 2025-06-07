/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The cocartesian monoidal category structure on commutative `R`-algebras

This file provides the cocartesian-monoidal category structure on `CommAlgCat R` constructed
explicitly using the tensor product.
-/

open CategoryTheory CartesianMonoidalCategory Limits TensorProduct

noncomputable section

namespace CommAlgCat
universe u v
variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R}

variable (A B) in
/-- The explicit cocone with tensor products as the fibered product in `CommAlgCat`. -/
def binaryCofan : BinaryCofan A B :=
  .mk (ofHom Algebra.TensorProduct.includeLeft)
    (ofHom (Algebra.TensorProduct.includeRight (A := A)))

variable (A B) in
@[simp]
lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom Algebra.TensorProduct.includeLeft := rfl

variable (A B) in
@[simp]
lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom Algebra.TensorProduct.includeRight := rfl

variable (A B) in
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

variable (A B) in
/-- Verify that the pushout cocone is indeed the colimit. -/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (Algebra.TensorProduct.lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine Algebra.TensorProduct.liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

/-- The initial object of `CommAlgCat R` is `R` as an algebra over itself -/
def isInitialSelf : IsInitial (of R R) := .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A))
  fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

open Opposite Algebra.TensorProduct CommAlgCat

attribute [local ext] Quiver.Hom.unop_inj

instance : MonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  tensorObj S T := op <| of R (S.unop ⊗[R] T.unop)
  whiskerLeft S {T₁ T₂} f := .op <| ofHom (Algebra.TensorProduct.map (.id _ _) f.unop.hom)
  whiskerRight {S₁ S₂} f T := .op <| ofHom (Algebra.TensorProduct.map f.unop.hom (.id _ _))
  tensorHom {S₁ S₂ T₁ T₂} f g := .op <| ofHom (map f.unop.hom g.unop.hom)
  tensorUnit := .op (.of R R)
  associator {S T U} := .op <| isoMk (Algebra.TensorProduct.assoc R R _ _ _).symm
  leftUnitor S := .op <| isoMk (Algebra.TensorProduct.lid R _).symm
  rightUnitor _ := .op <| isoMk (Algebra.TensorProduct.rid R R _).symm
  tensorHom_def := by intros; ext <;> rfl
  tensor_id := by intros; ext <;> rfl
  tensor_comp := by intros; ext <;> rfl
  whiskerLeft_id := by intros; ext <;> rfl
  id_whiskerRight := by intros; ext <;> rfl
  associator_naturality := by intros; ext <;> rfl
  leftUnitor_naturality := by intros; rfl
  rightUnitor_naturality := by intros; rfl
  pentagon := by intros; ext <;> rfl
  triangle := by intros; ext <;> rfl

instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
  tensorProductIsBinaryProduct S T :=
    BinaryCofan.IsColimit.op <| binaryCofanIsColimit (unop S) (unop T)
  fst_def S T := by ext x; show x ⊗ₜ 1 = x ⊗ₜ algebraMap R (unop T:) 1; simp
  snd_def S T := by ext x; show 1 ⊗ₜ x = algebraMap R (unop S:) 1 ⊗ₜ x; simp

instance : BraidedCategory (CommAlgCat.{u} R)ᵒᵖ where
  braiding S T := .op <| isoMk (Algebra.TensorProduct.comm R _ _)
  braiding_naturality_right := by intros; ext <;> rfl
  braiding_naturality_left := by intros; ext <;> rfl
  hexagon_forward S T U := by ext <;> rfl
  hexagon_reverse S T U := by ext <;> rfl

open MonoidalCategory

variable {A B C D : (CommAlgCat.{u} R)ᵒᵖ}

@[simp] lemma rightWhisker_hom (f : A ⟶ B) :
    (f ▷ C).unop.hom = Algebra.TensorProduct.map f.unop.hom (.id _ _) := rfl

@[simp] lemma leftWhisker_hom (f : A ⟶ B) :
    (C ◁ f).unop.hom = Algebra.TensorProduct.map (.id _ _) f.unop.hom := rfl

@[simp] lemma associator_hom_unop_hom :
    (α_ A B C).hom.unop.hom =
      (Algebra.TensorProduct.assoc R R A.unop B.unop C.unop).symm.toAlgHom := rfl

@[simp] lemma associator_inv_unop_hom :
    (α_ A B C).inv.unop.hom = (Algebra.TensorProduct.assoc R R A.unop B.unop C.unop).toAlgHom := rfl

@[simp] lemma braiding_hom_unop_hom :
    (β_ A B).hom.unop.hom = (Algebra.TensorProduct.comm R B.unop A.unop).toAlgHom := rfl

@[simp] lemma braiding_inv_unop_hom :
    (β_ A B).inv.unop.hom = (Algebra.TensorProduct.comm R A.unop B.unop).toAlgHom := rfl

@[simp] lemma tensorHom_unop_hom (f : A ⟶ C) (g : B ⟶ D) :
    (f ⊗ g).unop.hom = Algebra.TensorProduct.map f.unop.hom g.unop.hom := rfl

@[simp] lemma toUnit_unop_hom (A : (CommAlgCat R)ᵒᵖ) :
    (toUnit A).unop.hom = algebraMap R A.unop := rfl

@[simp] lemma fst_unop_hom (A B : (CommAlgCat R)ᵒᵖ) :
    (fst A B).unop.hom = Algebra.TensorProduct.includeLeft := rfl

@[simp] lemma snd_unop_hom (A B : (CommAlgCat R)ᵒᵖ) :
    (snd A B).unop.hom = Algebra.TensorProduct.includeRight := rfl

@[simp] lemma lift_unop_hom (f : C ⟶ A) (g : C ⟶ B) :
    (lift f g).unop.hom = Algebra.TensorProduct.lift f.unop.hom g.unop.hom (fun _ _ ↦ .all _ _) :=
  rfl

end CommAlgCat
