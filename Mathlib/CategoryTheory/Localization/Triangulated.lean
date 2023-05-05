import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Triangulated

namespace CategoryTheory

open Category Limits Pretriangulated

class MorphismProperty.IsCompatibleWithShift {C : Type _} [Category C]
  (W : MorphismProperty C) (A : Type _) [AddMonoid A] [HasShift C A] : Prop :=
(translate : ∀ (a : A), W.inverseImage (shiftFunctor C a) = W)

lemma MorphismProperty.iff_of_isCompatibleWithShift {C : Type _} [Category C]
    (W : MorphismProperty C) {A : Type _} [AddMonoid A] [HasShift C A]
    [W.IsCompatibleWithShift A]
    {X Y : C} (f : X ⟶ Y) (a : A) : W ((shiftFunctor C a).map f) ↔ W f := by
  conv_rhs => rw [← @IsCompatibleWithShift.translate _ _ W A _ _ _ a]

section

variable {C : Type _} [Category C]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive ] [Pretriangulated C]

class MorphismProperty.IsCompatibleWithTriangulation (W : MorphismProperty C) : Prop :=
  condition : ∀ (T₁ T₂ : Triangle C) (_ : T₁ ∈ distTriang C) (_ : T₂ ∈ distTriang C)
  (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (_ : W a) (_ : W b)
  (_ : T₁.mor₁ ≫ b = a ≫ T₂.mor₁), ∃ (c : T₁.obj₃ ⟶ T₂.obj₃) (_ : W c),
  (T₁.mor₂ ≫ c = b ≫ T₂.mor₂) ∧ (T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃)

end

namespace Triangulated

variable {C D : Type _} [Category C] [Category D]
  [HasShift C ℤ] [Preadditive C] [HasZeroObject C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive ] [Pretriangulated C]
  [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
    [∀ (n : ℤ), (shiftFunctor D n).Additive]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [L.Additive]
    [L.HasCommShift ℤ]  [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]
    [W.IsCompatibleWithShift ℤ] [W.IsCompatibleWithTriangulation]

namespace Localization

def distinguishedTriangles : Set (Triangle D) :=
  fun T => ∃ (T' : Triangle C) (_ : T ≅ L.mapTriangle.obj T'), T' ∈ distTriang C

lemma isomorphic_distinguished {T₁ T₂ : Triangle D} (e : T₂ ≅ T₁)
    (h : T₁ ∈ distinguishedTriangles L) : T₂ ∈ distinguishedTriangles L := by
  obtain ⟨T', e', hT'⟩ := h
  exact ⟨T', e ≪≫ e', hT'⟩

lemma contractible_distinguished (X : D) :
  contractibleTriangle X ∈ distinguishedTriangles L := by
  have := Localization.essSurj L W
  refine' ⟨contractibleTriangle (L.objPreimage X), _, Pretriangulated.contractible_distinguished _⟩
  exact ((contractibleTriangleFunctor D).mapIso (L.objObjPreimageIso X)).symm ≪≫
    Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) L.mapZeroObject.symm (by simp) (by simp) (by simp)

lemma pretriangulated : Pretriangulated D where
  distinguishedTriangles := distinguishedTriangles L
  isomorphic_distinguished := fun T₁ hT₁ T₂ e => isomorphic_distinguished L e hT₁
  contractible_distinguished := contractible_distinguished L W
  distinguished_cocone_triangle := sorry
  rotate_distinguished_triangle := sorry
  complete_distinguished_triangle_morphism := sorry

end Localization

end Triangulated

end CategoryTheory
