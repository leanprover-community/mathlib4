/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Comma.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types

/-!
# Colimit of representables

This file constructs an adjunction `Presheaf.yonedaAdjunction` between `(Cᵒᵖ ⥤ Type u)` and
`ℰ` given a functor `A : C ⥤ ℰ`, where the right adjoint `restrictedYoneda`
sends `(E : ℰ)` to `c ↦ (A.obj c ⟶ E)`, and the left adjoint `(Cᵒᵖ ⥤ Type v₁) ⥤ ℰ`
is a pointwise left Kan extension of `A` along the Yoneda embedding, which
exists provided `ℰ` has colimits)

We also show that every presheaf is a colimit of representables. This result
is also known as the density theorem, the co-Yoneda lemma and
the Ninja Yoneda lemma. Two formulations are given:
* `colimitOfRepresentable` uses the category of elements of a functor to types;
* `isColimitTautologicalCocone` uses the category of costructured arrows.

In the lemma `isLeftKanExtension_along_yoneda_iff`, we show that
if `L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ)` and `α : A ⟶ yoneda ⋙ L`, then
`α` makes `L` the left Kan extension of `L` along yoneda if and only if
`α` is an isomorphism (i.e. `L` extends `A`) and `L` preserves colimits.
`uniqueExtensionAlongYoneda` shows `yoneda.leftKanExtension A` is unique amongst
functors preserving colimits with this property, establishing the
presheaf category as the free cocompletion of a category.

Given a functor `F : C ⥤ D`, we also show construct an
isomorphism `compYonedaIsoYonedaCompLan : F ⋙ yoneda ≅ yoneda ⋙ F.op.lan`, and
show that it makes `F.op.lan` a left Kan extension of `F ⋙ yoneda`.

## Tags
colimit, representable, presheaf, free cocompletion

## References
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* https://ncatlab.org/nlab/show/Yoneda+extension
-/

namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Presheaf.ULift

variable {C : Type u₁} [Category.{v₁} C]

variable {ℰ : Type u₂} [Category.{v₂} ℰ] (A : C ⥤ ℰ)

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps!]
def restrictedYoneda : ℰ ⥤ Cᵒᵖ ⥤ Type (max v₁ v₂) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₁, v₂} ⋙
    (whiskeringLeft _ _ (Type (max v₁ v₂))).obj (Functor.op A)

/-- Auxiliary definition for `restrictedYonedaHomEquiv`. -/
def restrictedYonedaHomEquiv' (P : Cᵒᵖ ⥤ Type (max v₁ v₂)) (E : ℰ) :
    (CostructuredArrow.proj (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor) P ⋙ A ⟶
      (Functor.const (CostructuredArrow (yoneda ⋙ (whiskeringRight _ _ _).obj
        uliftFunctor) P)).obj E) ≃
      (P ⟶ (restrictedYoneda A).obj E) where
  toFun f :=
    { app := fun X x => ⟨f.app (CostructuredArrow.mk ((yonedaCompUliftFunctorEquiv _ _).symm x))⟩
      naturality := fun {X₁ X₂} φ => by sorry }
        -- ext x
        -- let ψ : CostructuredArrow.mk ((yonedaCompUliftFunctorEquiv _ _).symm (P.toPrefunctor.map φ x)) ⟶
        --   CostructuredArrow.mk ((yonedaCompUliftFunctorEquiv _ _).symm x) := CostructuredArrow.homMk φ.unop (by
        --     dsimp [yonedaEquiv]
        --     aesop_cat )
        -- simpa using (f.naturality ψ).symm }
  invFun g :=
    { app := fun y => (yonedaCompUliftFunctorEquiv _ _ (y.hom ≫ g)).1
      naturality := fun {X₁ X₂} φ => by sorry }
        -- dsimp
        -- rw [← CostructuredArrow.w φ]
        -- dsimp [yonedaEquiv]
        -- simp only [comp_id, id_comp]
        -- refine (congr_fun (g.naturality φ.left.op) (X₂.hom.app (Opposite.op X₂.left)
        --   (𝟙 _))).symm.trans ?_
        -- dsimp
        -- apply congr_arg
        -- simpa using congr_fun (X₂.hom.naturality φ.left.op).symm (𝟙 _) }
  left_inv f := by sorry
    -- ext ⟨X, ⟨⟨⟩⟩, φ⟩
    -- suffices yonedaEquiv.symm (φ.app (Opposite.op X) (𝟙 X)) = φ by
    --   dsimp
    --   erw [yonedaEquiv_apply]
    --   dsimp [CostructuredArrow.mk]
    --   erw [this]
    -- exact yonedaEquiv.injective (by aesop_cat)
  right_inv g := by sorry
    -- ext X x
    -- dsimp
    -- erw [yonedaEquiv_apply]
    -- dsimp
    -- rw [yonedaEquiv_symm_app_apply]
    -- simp

section

example [HasColimitsOfSize.{v₁, max u₁ v₁} ℰ] :
    yoneda.HasPointwiseLeftKanExtension A := inferInstance

variable [(yoneda ⋙ (whiskeringRight _ _ _).obj
  uliftFunctor.{v₂, v₁}).HasPointwiseLeftKanExtension A]

variable {A}
variable (L : (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ ℰ)
    (α : A ⟶ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor) ⋙ L)
    [L.IsLeftKanExtension α]


/-- Auxiliary definition for `yonedaAdjunction`. -/
noncomputable def restrictedYonedaHomEquiv
    (α : A ⟶ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor) ⋙ L)
    [L.IsLeftKanExtension α] (P : Cᵒᵖ ⥤ Type (max v₁ v₂)) (E : ℰ) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedYoneda A).obj E) :=
  ((Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv E).trans
    (restrictedYonedaHomEquiv' A P E)

/-- If `L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type v₁` -/
noncomputable def yonedaAdjunction : L ⊣ restrictedYoneda A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedYonedaHomEquiv L α
      homEquiv_naturality_left_symm := fun {P Q X} f g => by sorry
        -- obtain ⟨g, rfl⟩ := (restrictedYonedaHomEquiv L α Q X).surjective g
        -- apply (restrictedYonedaHomEquiv L α P X).injective
        -- simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        -- ext Y y
        -- dsimp [restrictedYonedaHomEquiv, restrictedYonedaHomEquiv', IsColimit.homEquiv]
        -- rw [assoc, assoc, ← L.map_comp_assoc]
        -- congr 3
        -- apply yonedaEquiv.injective
        -- simp [yonedaEquiv]
      homEquiv_naturality_right := fun {P X Y} f g => by sorry }
        -- apply (restrictedYonedaHomEquiv L α P Y).symm.injective
        -- simp only [Equiv.symm_apply_apply]
        -- dsimp [restrictedYonedaHomEquiv, restrictedYonedaHomEquiv', IsColimit.homEquiv]
        -- apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        -- intro p
        -- rw [IsColimit.fac]
        -- dsimp [restrictedYoneda, yonedaEquiv]
        -- simp only [assoc]
        -- congr 3
        -- apply yonedaEquiv.injective
        -- simp [yonedaEquiv] }

/-- Any left Kan extension along the Yoneda embedding preserves colimits. -/
noncomputable def preservesColimitsOfSizeOfIsLeftKanExtension :
    PreservesColimitsOfSize.{v₃, u₃} L :=
  (yonedaAdjunction L α).leftAdjointPreservesColimits

lemma isIso_of_isLeftKanExtension : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α).isIso_hom

variable (A)

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
noncomputable instance preservesColimitsOfSizeLeftKanExtension' :
    PreservesColimitsOfSize.{v₃, u₃}
      ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}).leftKanExtension A) :=
  (yonedaAdjunction _ ((yoneda ⋙ (whiskeringRight _ _ _).obj
    uliftFunctor.{v₂, v₁}).leftKanExtensionUnit A)).leftAdjointPreservesColimits

end

/-- A functor to the presheaf category in which everything in the image is representable (witnessed
by the fact that it factors through the yoneda embedding).
`coconeOfRepresentable` gives a cocone for this functor which is a colimit and has point `P`.
-/
@[reducible]
def functorToRepresentables (P : Cᵒᵖ ⥤ Type (max v₁ v₂)) : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type (max v₁ v₂) :=
  (CategoryOfElements.π P).leftOp ⋙ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁})

variable {A : C ⥤ ℰ}

example [HasColimitsOfSize.{v₁, max u₁ v₁} ℰ] :
    yoneda.HasPointwiseLeftKanExtension A :=
  inferInstance

variable
  [(yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}).HasPointwiseLeftKanExtension A]

section

variable (L : (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ ℰ)
  (α : A ⟶ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor) ⋙ L)

instance [L.IsLeftKanExtension α] : IsIso α :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α).isIso_hom

lemma isLeftKanExtension_along_yoneda_iff :
    L.IsLeftKanExtension α ↔
      (IsIso α ∧ Nonempty (PreservesColimitsOfSize.{v₂, max u₁ v₁} L)) := by
  constructor
  · intro
    exact ⟨inferInstance, ⟨preservesColimitsOfNatIso
      (Functor.leftKanExtensionUnique _
        ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor).leftKanExtensionUnit A) _ α)⟩⟩
  · rintro ⟨_, ⟨_⟩⟩
    apply Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
      (E := Functor.LeftExtension.mk _ α)
    intro P
    dsimp [Functor.LeftExtension.IsPointwiseLeftKanExtensionAt]
    apply IsColimit.ofWhiskerEquivalence
      (CategoryOfElements.costructuredArrowYonedaEquivalenceULift _)
    let e : CategoryOfElements.toCostructuredArrowULift P ⋙ CostructuredArrow.proj
        ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor)) P ⋙ A ≅
        functorToRepresentables.{v₁, v₂} P ⋙ L := sorry
      -- isoWhiskerLeft _ (isoWhiskerLeft _ (asIso α)) ≪≫
      --   isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      --   (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Iso.refl _) L
    sorry
    -- apply (IsColimit.precomposeHomEquiv e.symm _).1
    -- exact IsColimit.ofIsoColimit (isColimitOfPreserves L (colimitOfRepresentable P))
    --   (Cocones.ext (Iso.refl _))

lemma isLeftKanExtension_of_preservesColimits
    (L : (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ ℰ)
      (e : A ≅ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}) ⋙ L)
    [PreservesColimitsOfSize.{v₂, max u₁ v₁} L] :
    L.IsLeftKanExtension e.hom := by
  rw [isLeftKanExtension_along_yoneda_iff]
  exact ⟨inferInstance, ⟨inferInstance⟩⟩

end

/-- Show that `yoneda.leftKanExtension A` is the unique colimit-preserving
functor which extends `A` to the presheaf category.

The second part of [MM92], Chapter I, Section 5, Corollary 4.
See Property 3 of https://ncatlab.org/nlab/show/Yoneda+extension#properties.
-/
noncomputable def uniqueExtensionAlongYoneda (L : (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ ℰ)
    (e : A ≅ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}) ⋙ L)
    [PreservesColimitsOfSize.{v₂, max u₁ v₁} L] : L ≅
      (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}).leftKanExtension A :=
  have := isLeftKanExtension_of_preservesColimits L e
  Functor.leftKanExtensionUnique _ e.hom _
    ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}).leftKanExtensionUnit A)

instance (L : (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ ℰ) [PreservesColimitsOfSize.{v₂, max u₁ v₁} L]
    [(yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}).HasPointwiseLeftKanExtension ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}) ⋙ L)] :
    L.IsLeftKanExtension (𝟙 _ :
      (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}) ⋙ L ⟶ _) :=
  isLeftKanExtension_of_preservesColimits _ (Iso.refl _)

/-- If `L` preserves colimits and `ℰ` has them, then it is a left adjoint. Note this is a (partial)
converse to `leftAdjointPreservesColimits`.
-/
lemma isLeftAdjoint_of_preservesColimits (L : (C ⥤ Type (max v₁ v₂)) ⥤ ℰ)
    [PreservesColimitsOfSize.{v₂, max u₁ v₁} L]
    [(yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}).HasPointwiseLeftKanExtension
      ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂, v₁}) ⋙
        (opOpEquivalence C).congrLeft.functor.comp L)] :
    L.IsLeftAdjoint :=
  ⟨_, ⟨((opOpEquivalence C).congrLeft.symm.toAdjunction.comp
    (yonedaAdjunction _ (𝟙 _))).ofNatIsoLeft ((opOpEquivalence C).congrLeft.invFunIdAssoc L)⟩⟩

end CategoryTheory.Presheaf.ULift
