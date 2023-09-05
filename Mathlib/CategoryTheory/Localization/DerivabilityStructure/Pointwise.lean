import Mathlib.CategoryTheory.Localization.DerivabilityStructure
import Mathlib.CategoryTheory.Functor.Derived.Pointwise
import Mathlib.CategoryTheory.Limits.Final

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

lemma Limits.hasColimit_iff_of_final {C C' D : Type*} [Category C] [Category C']
    [Category D] (F : C ⥤ C') (G : C' ⥤ D) [F.Final]:
    HasColimit (F ⋙ G) ↔ HasColimit G := by
  constructor
  · intro
    exact Functor.Final.hasColimit_of_comp F
  · intro
    infer_instance

lemma Limits.hasColimit_iff_of_iso {J C : Type*} [Category J] [Category C]
    {F G : J ⥤ C} (e : F ≅ G) : HasColimit F ↔ HasColimit G := by
  constructor
  · intro
    exact hasColimitOfIso e.symm
  · intro
    exact hasColimitOfIso e

open Limits


variable {C₁ : Type u₁} {C₂ : Type u₂} {H : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂) [Φ.IsRightDerivabilityStructure]

-- similar to Kahn-Maltsiniotis Lemme 5.5
lemma hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure (F : C₂ ⥤ H) (X : C₁) :
    (Φ.functor ⋙ F).HasPointwiseRightDerivedFunctorAt W₁ X ↔
      F.HasPointwiseRightDerivedFunctorAt W₂ (Φ.functor.obj X) := by
  let e : W₂.Q.obj _ ≅ (Φ.localizedFunctor W₁.Q W₂.Q).obj _  := ((Φ.catCommSq W₁.Q W₂.Q).iso).app X
  rw [F.hasPointwiseRightDerivedFunctorAt_iff W₂.Q W₂ (Φ.functor.obj X),
    (Φ.functor ⋙ F).hasPointwiseRightDerivedFunctorAt_iff W₁.Q W₁ X]
  rw [F.hasPointwiseLeftKanExtensionAt_iff_of_iso W₂.Q e]
  dsimp [Functor.HasPointwiseLeftKanExtensionAt]
  let w : TwoSquare _ _ _ _ := ((Φ.catCommSq W₁.Q W₂.Q).iso).hom
  have h : w.GuitartExact := inferInstance
  rw [← hasColimit_iff_of_final (w.costructuredArrowRightwards (W₁.Q.obj X))]
  apply hasColimit_iff_of_iso
  apply Iso.refl

lemma hasPointwiseRightDerivedFunctor_iff_of_isRightDerivabilityStructure (F : C₂ ⥤ H) :
    F.HasPointwiseRightDerivedFunctor W₂ ↔
      ((Φ.functor ⋙ F).HasPointwiseRightDerivedFunctor W₁) := by
  constructor
  · intro hF X₁
    rw [hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure]
    apply hF
  · intro hF X₂
    have R : Φ.RightResolution X₂ := Classical.arbitrary _
    simpa only [hasPointwiseRightDerivedFunctorAt_iff_of_isRightDerivabilityStructure,
      ← F.hasPointwiseRightDerivedFunctorAt_iff_of_mem W₂ R.w R.hw ] using hF R.X₁

-- TODO: comparison iso when the conditions above are satisfied
-- TODO: if `(Φ.functor ⋙ F)` inverts `W₁`, then we can compute trivially
-- the derived functors on objects coming from `C₁`

end LocalizerMorphism

end CategoryTheory
