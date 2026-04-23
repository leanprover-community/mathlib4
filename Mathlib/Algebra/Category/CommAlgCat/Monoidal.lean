/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The co-Cartesian monoidal category structure on commutative `R`-algebras

This file provides the co-Cartesian-monoidal category structure on `CommAlgCat R` constructed
explicitly using the tensor product.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits TensorProduct Opposite
open Algebra.TensorProduct
open Algebra.TensorProduct (lid rid assoc comm)

noncomputable section

namespace CommAlgCat
universe u v
variable {R : Type u} [CommRing R] {A B C D : CommAlgCat.{u} R}

variable (A B)

/-- The explicit cocone with tensor products as the fibered coproduct in `CommAlgCat`. -/
def binaryCofan : BinaryCofan A B := .mk (ofHom includeLeft) (ofHom <| includeRight (A := A))

@[simp] lemma binaryCofan_inl : (binaryCofan A B).inl = ofHom includeLeft := rfl
@[simp] lemma binaryCofan_inr : (binaryCofan A B).inr = ofHom includeRight := rfl
@[simp] lemma binaryCofan_pt : (binaryCofan A B).pt = .of R (A ⊗[R] B) := rfl

/-- Verify that the pushout cocone is indeed the colimit. -/
def binaryCofanIsColimit : IsColimit (binaryCofan A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ofHom (lift f.hom g.hom fun _ _ ↦ .all _ _))
    (fun f g ↦ by ext1; exact lift_comp_includeLeft _ _ fun _ _ ↦ .all _ _)
    (fun f g ↦ by ext1; exact lift_comp_includeRight _ _ fun _ _ ↦ .all _ _)
    (fun f g m hm₁ hm₂ ↦ by
      ext1
      refine liftEquiv.symm_apply_eq (y := ⟨⟨_, _⟩, fun _ _ ↦ .all _ _⟩).mp ?_
      exact Subtype.ext (Prod.ext congr(($hm₁).hom) congr(($hm₂).hom)))

/-- The initial object of `CommAlgCat R` is `R` as an algebra over itself. -/
def isInitialSelf : IsInitial (of R R) :=
  .ofUniqueHom (fun A ↦ ofHom (Algebra.ofId R A)) fun _ _ ↦ hom_ext (Algebra.ext_id _ _ _)

attribute [local simp] one_def in
instance : MonoidalCategory (CommAlgCat.{u} R) where
  tensorObj S T := of R (S ⊗[R] T)
  whiskerLeft _ {_ _} f := ofHom (map (.id _ _) f.hom)
  whiskerRight f T := ofHom (map f.hom (.id _ _))
  tensorHom f g := ofHom (map f.hom g.hom)
  tensorUnit := .of R R
  associator _ _ _ := isoMk (assoc R R R _ _ _)
  leftUnitor _ := isoMk (lid R _)
  rightUnitor _ := isoMk (rid R R _)

@[simp] lemma coe_tensorUnit : 𝟙_ (CommAlgCat.{u} R) = R := rfl

@[simp] lemma coe_tensorObj : A ⊗ B = A ⊗[R] B := rfl

variable {A B}

@[simp] lemma tensorHom_hom (f : A ⟶ C) (g : B ⟶ D) : (f ⊗ₘ g).hom = map f.hom g.hom := rfl

variable (C) in
@[simp] lemma whiskerRight_hom (f : A ⟶ B) : (f ▷ C).hom = map f.hom (.id _ _) := rfl

variable (C) in
@[simp] lemma whiskerLeft_hom (f : A ⟶ B) : (C ◁ f).hom = map (.id _ _) f.hom := rfl

variable (A B C) in
@[simp] lemma associator_hom_hom : (α_ A B C).hom.hom = (assoc R R R A B C).toAlgHom := rfl

variable (A B C) in
@[simp] lemma associator_inv_hom : (α_ A B C).inv.hom = (assoc R R R A B C).symm.toAlgHom := rfl

instance : BraidedCategory (CommAlgCat.{u} R) where
  braiding S T := isoMk (comm R _ _)
  braiding_naturality_right := by intros; ext : 1; dsimp; ext <;> rfl
  braiding_naturality_left := by intros; ext : 1; dsimp; ext <;> rfl
  hexagon_forward S T U := by ext : 1; dsimp; ext <;> rfl
  hexagon_reverse S T U := by ext : 1; dsimp; ext <;> rfl

variable (A B) in
@[simp] lemma braiding_hom_hom : (β_ A B).hom.hom = (comm R A B).toAlgHom := rfl

variable (A B) in
@[simp] lemma braiding_inv_hom : (β_ A B).inv.hom = (comm R B A).toAlgHom := rfl

attribute [local ext] Quiver.Hom.unop_inj in
instance : CartesianMonoidalCategory (CommAlgCat.{u} R)ᵒᵖ where
  isTerminalTensorUnit := terminalOpOfInitial isInitialSelf
  fst := _
  snd := _
  tensorProductIsBinaryProduct S T := BinaryCofan.IsColimit.op <| binaryCofanIsColimit S.unop T.unop
  fst_def S T := by ext x; change x ⊗ₜ 1 = x ⊗ₜ algebraMap R T.unop 1; simp
  snd_def S T := by ext x; change 1 ⊗ₜ x = algebraMap R S.unop 1 ⊗ₜ x; simp

variable {A B C D : (CommAlgCat.{u} R)ᵒᵖ}

@[simp] lemma fst_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (fst A B).unop.hom = includeLeft := rfl
@[simp] lemma snd_unop_hom (A B : (CommAlgCat.{u} R)ᵒᵖ) : (snd A B).unop.hom = includeRight := rfl

variable (A B) in
@[simp] lemma toUnit_unop_hom : (toUnit A).unop.hom = Algebra.ofId R A.unop := rfl

@[simp] lemma lift_unop_hom (f : C ⟶ A) (g : C ⟶ B) :
    (lift f g).unop.hom = lift f.unop.hom g.unop.hom fun _ _ ↦ .all _ _ := rfl

end CommAlgCat
