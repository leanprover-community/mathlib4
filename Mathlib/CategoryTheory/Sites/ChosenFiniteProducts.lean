/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.ChosenFiniteProducts.FunctorCategory

/-!
# Chosen finite products on sheaves

In this file, we put a `ChosenFiniteProducts` instance on `A`-valued sheaves for a
`GrothendieckTopology` whenever `A` has a ChosenFiniteProducts instance.
-/


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)
variable [ChosenFiniteProducts A]

namespace Sheaf

variable (X Y : Sheaf J A)

lemma tensorProd_isSheaf : Presheaf.IsSheaf J (X.val ⊗ Y.val) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (pairComp X Y (sheafToPresheaf J A)).inv).obj
    (ChosenFiniteProducts.product X.val Y.val).cone)
  exact (IsLimit.postcomposeInvEquiv _ _).invFun (ChosenFiniteProducts.product X.val Y.val).isLimit

lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (Functor.uniqueFromEmpty _).inv).obj
    ChosenFiniteProducts.terminal.cone)
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun ChosenFiniteProducts.terminal.isLimit
  · exact Functor.empty _

/-- Any `ChosenFiniteProducts` on `A` induce a `ChosenFiniteProducts` structures on `A`-valued
sheaves. -/
@[simps! product_cone_pt_val terminal_cone_pt_val_obj terminal_cone_pt_val_map]
noncomputable instance : ChosenFiniteProducts (Sheaf J A) where
  product X Y :=
    { cone := BinaryFan.mk
          (P := { val := X.val ⊗ Y.val
                  cond := tensorProd_isSheaf J X Y})
          ⟨(ChosenFiniteProducts.fst _ _)⟩ ⟨(ChosenFiniteProducts.snd _ _)⟩
      isLimit :=
        { lift := fun f ↦ ⟨ChosenFiniteProducts.lift (BinaryFan.fst f).val (BinaryFan.snd f).val⟩
          fac := by rintro s ⟨⟨j⟩⟩ <;> apply Sheaf.hom_ext <;> simp
          uniq := by
            intro x f h
            apply Sheaf.hom_ext
            apply ChosenFiniteProducts.hom_ext
            · specialize h ⟨WalkingPair.left⟩
              rw [Sheaf.hom_ext_iff] at h
              simpa using h
            · specialize h ⟨WalkingPair.right⟩
              rw [Sheaf.hom_ext_iff] at h
              simpa using h } }
  terminal :=
    { cone := asEmptyCone { val := 𝟙_ (Cᵒᵖ ⥤ A)
                            cond := tensorUnit_isSheaf _}
      isLimit :=
        { lift := fun f ↦ ⟨ChosenFiniteProducts.toUnit f.pt.val⟩
          fac := by intro s ⟨e⟩; cases e
          uniq := by
            intro x f h
            apply Sheaf.hom_ext
            exact ChosenFiniteProducts.toUnit_unique f.val _} }

@[simp]
lemma fst_val : (ChosenFiniteProducts.fst X Y).val = ChosenFiniteProducts.fst X.val Y.val := rfl

@[simp]
lemma snd_val : (ChosenFiniteProducts.snd X Y).val = ChosenFiniteProducts.snd X.val Y.val := rfl

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)

@[simp]
lemma lift_val : (ChosenFiniteProducts.lift f g).val = ChosenFiniteProducts.lift f.val g.val := rfl

@[simp]
lemma whiskerLeft_val : (X ◁ f).val = (X.val ◁ f.val) := rfl
@[simp]
lemma whiskerRight_val : (f ▷ X).val = (f.val ▷ X.val) := rfl

/-- The inclusion from sheaves to presheaves is monoidal with respect to the cartesian monoidal
structures. -/
@[simps!]
noncomputable def monoidalSheafToPresheaf : MonoidalFunctor (Sheaf J A) (Cᵒᵖ ⥤ A) :=
  Functor.toMonoidalFunctorOfChosenFiniteProducts (sheafToPresheaf J A)

end CategoryTheory.Sheaf
