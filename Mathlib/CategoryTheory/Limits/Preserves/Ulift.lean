import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Types

universe v u

open CategoryTheory Limits

def sectionsEquiv {J : Type u} [Category.{u, u} J] (K : J ⥤ Type u) :
    uliftFunctor.{v, u}.obj (Functor.sections K) ≃ (Functor.sections (K ⋙ uliftFunctor.{v, u})) where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩
  left_inv := by intro; apply ULift.ext; ext; rfl
  right_inv := by intro; ext; rfl

noncomputable instance : CreatesLimitsOfSize.{u, u} uliftFunctor.{v, u} where
  CreatesLimitsOfShape := {
    CreatesLimit := fun {K} =>
      @createsLimitOfFullyFaithfulOfIso _ _ _ _ _ _ K uliftFunctor _ _ _ (limit K)
        (uliftFunctor.{v, u}.mapIso (equivEquivIso (Types.isLimitEquivSections.{u, u}
        (limit.isLimit K))) ≪≫ (equivEquivIso (sectionsEquiv K)) ≪≫
        (equivEquivIso (Types.isLimitEquivSections.{u, max u v}
        (limit.isLimit (K ⋙ uliftFunctor.{v, u})))).symm) }

noncomputable instance : PreservesLimitsOfSize.{u, u} uliftFunctor := inferInstance
