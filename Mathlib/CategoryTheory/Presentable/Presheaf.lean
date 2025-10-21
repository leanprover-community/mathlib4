/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Categories of presheaves are locally presentable

If `A` is a locally `κ`-presentable category and `C` is a small category,
we show that `Cᵒᵖ ⥤ A` is also locally `κ`-presentable, under the
additional assumption that `A` has pullbacks (a condition which should
be automatically satisfied (TODO)).

-/

universe w v v' u u'

namespace CategoryTheory

open Opposite Limits

namespace Presheaf

attribute [local simp] freeYonedaHomEquiv_comp in
instance {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
    [HasColimitsOfSize.{w, w} A] [HasCoproducts.{v} A]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] (X : C) (M : A)
    [IsCardinalPresentable M κ] :
    IsCardinalPresentable (freeYoneda X M) κ := by
  let e : coyoneda.obj (op (freeYoneda X M)) ≅
      (evaluation Cᵒᵖ A).obj (op X) ⋙ coyoneda.obj (op M) ⋙ uliftFunctor.{u} :=
    NatIso.ofComponents (fun P ↦ Equiv.toIso (freeYonedaHomEquiv.trans Equiv.ulift.symm))
  constructor
  intro J _ _
  have := preservesColimitsOfShape_of_isCardinalPresentable M κ J
  exact preservesColimitsOfShape_of_natIso e.symm

lemma isStrongGenerator
    {A : Type u'} [Category.{v'} A] {P : ObjectProperty A} (hP : P.IsStrongGenerator)
    [HasCoproducts.{w} A] [HasPullbacks A] (C : Type w) [SmallCategory C] :
    (ObjectProperty.ofObj (fun (T : C × (Subtype P)) ↦
      freeYoneda T.1 T.2.1)).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff] at hP ⊢
  obtain ⟨hP₁, hP₂⟩ := hP
  refine ⟨Presheaf.isSeparating (C := C) (ι := Subtype P) (S := Subtype.val)
    (by simpa using hP₁),
    fun P₁ P₂ i _ hi ↦ ?_⟩
  · rw [NatTrans.isIso_iff_isIso_app]
    rintro ⟨X⟩
    refine hP₂ _ (fun G hG f ↦ ?_)
    obtain ⟨y, rfl⟩ := freeYonedaHomEquiv.surjective f
    obtain ⟨x, rfl⟩ := hi (freeYoneda X G)
      (ObjectProperty.ofObj_apply (fun (T : C × (Subtype P)) ↦
        freeYoneda T.1 T.2.1) ⟨X, G, hG⟩) y
    exact ⟨freeYonedaHomEquiv x, by simp [freeYonedaHomEquiv_comp]⟩

instance {A : Type u'} [Category.{v'} A] [LocallySmall.{w} A] (C : Type w) [SmallCategory C] :
    LocallySmall.{w} (C ⥤ A) where
  hom_small P Q :=
    small_of_injective (f := NatTrans.app) (fun f g h ↦ by aesop)

instance {A : Type u'} [Category.{v'} A] (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [IsCardinalLocallyPresentable A κ] [HasPullbacks A]
    (C : Type w) [SmallCategory C] :
    IsCardinalLocallyPresentable (Cᵒᵖ ⥤ A) κ := by
  have hA := (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator A κ).1 inferInstance
  obtain ⟨P, _, hP₁, hP₂⟩ := hA
  rw [IsCardinalLocallyPresentable.iff_exists_isStrongGenerator]
  refine ⟨_, inferInstance, isStrongGenerator hP₁ C, ?_⟩
  rintro _ ⟨X, G, hG⟩
  have := hP₂ _ hG
  rw [isCardinalPresentable_iff] at this ⊢
  infer_instance

instance {A : Type u'} [Category.{v'} A] [IsLocallyPresentable.{w} A] [HasPullbacks A]
    (C : Type w) [SmallCategory C] :
    IsLocallyPresentable.{w} (Cᵒᵖ ⥤ A) where
  exists_cardinal := by
    obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} A
    exact ⟨κ, inferInstance, inferInstance⟩

example (C : Type w) [SmallCategory C] :
    IsLocallyPresentable.{w} (Cᵒᵖ ⥤ Type w) := inferInstance

end Presheaf

end CategoryTheory
