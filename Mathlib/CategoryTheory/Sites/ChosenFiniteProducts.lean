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
`GrothendieckTopology` whenever `A` has a `ChosenFiniteProducts` instance.
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
    (BinaryFan.mk (ChosenFiniteProducts.fst X.val Y.val) (ChosenFiniteProducts.snd _ _)))
  exact (IsLimit.postcomposeInvEquiv _ _).invFun
    (ChosenFiniteProducts.tensorProductIsBinaryProduct X.val Y.val)

lemma tensorUnit_isSheaf : Presheaf.IsSheaf J (𝟙_ (Cᵒᵖ ⥤ A)) := by
  apply isSheaf_of_isLimit (E := (Cones.postcompose (Functor.uniqueFromEmpty _).inv).obj
    (asEmptyCone (𝟙_ _)))
  · exact (IsLimit.postcomposeInvEquiv _ _).invFun ChosenFiniteProducts.isTerminalTensorUnit
  · exact Functor.empty _

/-- Any `ChosenFiniteProducts` on `A` induce a
`ChosenFiniteProducts` structure on `A`-valued sheaves. -/
noncomputable instance chosenFiniteProducts : ChosenFiniteProducts (Sheaf J A) :=
  .ofChosenFiniteProducts
   ({ cone := asEmptyCone { val := 𝟙_ (Cᵒᵖ ⥤ A), cond := tensorUnit_isSheaf _}
      isLimit.lift f := ⟨ChosenFiniteProducts.toUnit f.pt.val⟩
      isLimit.fac := by rintro _ ⟨⟨⟩⟩
      isLimit.uniq x f h := Sheaf.hom_ext _ _ (ChosenFiniteProducts.toUnit_unique f.val _) })
  fun X Y ↦
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

@[simp]
lemma chosenFiniteProducts_fst_val : (ChosenFiniteProducts.fst X Y).val =
    ChosenFiniteProducts.fst X.val Y.val := rfl

@[simp]
lemma chosenFiniteProducts_snd_val : (ChosenFiniteProducts.snd X Y).val =
    ChosenFiniteProducts.snd X.val Y.val := rfl

variable {X Y}
variable {W : Sheaf J A} (f : W ⟶ X) (g : W ⟶ Y)

@[simp]
lemma chosenFiniteProducts_lift_val : (ChosenFiniteProducts.lift f g).val =
    ChosenFiniteProducts.lift f.val g.val := rfl

@[simp]
lemma chosenFiniteProducts_whiskerLeft_val : (X ◁ f).val = (X.val ◁ f.val) := rfl
@[simp]
lemma chosenFiniteProducts_whiskerRight_val : (f ▷ X).val = (f.val ▷ X.val) := rfl

end Sheaf

/-- The inclusion from sheaves to presheaves is monoidal with respect to the cartesian monoidal
structures. -/
noncomputable instance sheafToPresheafMonoidal : (sheafToPresheaf J A).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun F G ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp]
lemma sheafToPresheaf_ε : ε (sheafToPresheaf J A) = 𝟙 _ := rfl
@[simp]
lemma sheafToPresheaf_η : η (sheafToPresheaf J A) = 𝟙 _ := rfl

variable {J}

@[simp]
lemma sheafToPresheaf_μ (X Y : Sheaf J A) : μ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl
@[simp]
lemma sheafToPresheaf_δ (X Y : Sheaf J A) : δ (sheafToPresheaf J A) X Y = 𝟙 _ := rfl

end CategoryTheory
