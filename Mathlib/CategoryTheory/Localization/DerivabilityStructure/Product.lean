/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Basic
import Mathlib.CategoryTheory.Localization.Prod

/-!
# Product of derivability structures

-/

namespace CategoryTheory

open Category Localization

variable {C₁ D₁ C₂ D₂ : Type*} {C₂ : Type*}
  [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {W₁ : MorphismProperty C₁} {W₁' : MorphismProperty D₁}
  {W₂ : MorphismProperty C₂} {W₂' : MorphismProperty D₂}

namespace LocalizerMorphism

variable (Φ₁ : LocalizerMorphism W₁ W₁') (Φ₂ : LocalizerMorphism W₂ W₂')

def prod : LocalizerMorphism (W₁.prod W₂) (W₁'.prod W₂') where
  functor := Φ₁.functor.prod Φ₂.functor
  map := fun _ _ ⟨f₁, f₂⟩ ⟨h₁, h₂⟩ => ⟨Φ₁.map f₁ h₁, Φ₂.map f₂ h₂⟩

variable {Φ₁ Φ₂}

def RightResolution.prod {X₁ : D₁} {X₂ : D₂} (R₁ : Φ₁.RightResolution X₁)
    (R₂ : Φ₂.RightResolution X₂) : (Φ₁.prod Φ₂).RightResolution ⟨X₁, X₂⟩ where
  X₁ := ⟨R₁.X₁, R₂.X₁⟩
  w := ⟨R₁.w, R₂.w⟩
  hw := ⟨R₁.hw, R₂.hw⟩

def LeftResolution.prod {X₁ : D₁} {X₂ : D₂} (R₁ : Φ₁.LeftResolution X₁)
    (R₂ : Φ₂.LeftResolution X₂) : (Φ₁.prod Φ₂).LeftResolution ⟨X₁, X₂⟩ where
  X₁ := ⟨R₁.X₁, R₂.X₁⟩
  w := ⟨R₁.w, R₂.w⟩
  hw := ⟨R₁.hw, R₂.hw⟩

variable (Φ₁ Φ₂)

instance [Φ₁.HasRightResolutions] [Φ₂.HasRightResolutions] :
    (Φ₁.prod Φ₂).HasRightResolutions := fun ⟨X₁, X₂⟩ => by
  refine ⟨RightResolution.prod ?_ ?_⟩
  all_goals apply Classical.arbitrary

instance [Φ₁.HasLeftResolutions] [Φ₂.HasLeftResolutions] :
    (Φ₁.prod Φ₂).HasLeftResolutions := fun ⟨X₁, X₂⟩ => by
  refine ⟨LeftResolution.prod ?_ ?_⟩
  all_goals apply Classical.arbitrary

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]
  [W₁'.ContainsIdentities] [W₂'.ContainsIdentities]

instance [Φ₁.IsRightDerivabilityStructure] [Φ₂.IsRightDerivabilityStructure] :
    (Φ₁.prod Φ₂).IsRightDerivabilityStructure := by
  rw [(Φ₁.prod Φ₂).isRightDerivabilityStructure_iff (W₁.Q.prod W₂.Q) (W₁'.Q.prod W₂'.Q)
    ((Φ₁.localizedFunctor W₁.Q W₁'.Q).prod (Φ₂.localizedFunctor W₂.Q W₂'.Q))
    (NatIso.prod (Φ₁.catCommSq W₁.Q W₁'.Q).iso (Φ₂.catCommSq W₂.Q W₂'.Q).iso)]
  have := Φ₁.guitartExact_of_isRightDerivabilityStructure W₁.Q W₁'.Q
  have := Φ₂.guitartExact_of_isRightDerivabilityStructure W₂.Q W₂'.Q
  apply TwoSquare.GuitartExact.prod

#check prodOpEquiv C₁ C₂

instance {D : Type*} [Category D] (L : C₁ᵒᵖ × C₂ᵒᵖ ⥤ D)
    [L.IsLocalization (W₁.op.prod W₂.op)] :
    ((prodOpEquiv C₁ C₂).functor ⋙ L).IsLocalization (W₁.prod W₂).op :=
  Functor.IsLocalization.of_equivalence_source L (W₁.op.prod W₂.op) _ (W₁.prod W₂).op
    (prodOpEquiv C₁ C₂).symm (by
      rintro _ _ _ ⟨h₁, h₂⟩
      simp only [Equivalence.symm_functor, MorphismProperty.inverseImage_iff]
      exact MorphismProperty.le_isoClosure _ _ ⟨h₁, h₂⟩) (by
      rintro _ _ _ ⟨h₁, h₂⟩
      exact Localization.inverts L (W₁.op.prod W₂.op) _ ⟨h₁, h₂⟩) (Iso.refl _)

instance [Φ₁.IsLeftDerivabilityStructure] [Φ₂.IsLeftDerivabilityStructure] :
    (Φ₁.prod Φ₂).IsLeftDerivabilityStructure := by
  rw [isLeftDerivabilityStructure_iff_op]
  let L := W₁.op.Q.prod W₂.op.Q
  let L' := W₁'.op.Q.prod W₂'.op.Q
  let F := (Φ₁.op.prod Φ₂.op).functor
  let F' := (Φ₁.op.prod Φ₂.op).localizedFunctor L L'
  let e : F ⋙ L' ≅ L ⋙ F' := ((Φ₁.op.prod Φ₂.op).catCommSq L L').iso
  have he := (Φ₁.op.prod Φ₂.op).guitartExact_of_isRightDerivabilityStructure' _ _ _ e
  let E := prodOpEquiv C₁ C₂
  let E' := prodOpEquiv D₁ D₂
  let w : (Φ₁.prod Φ₂).op.functor ⋙ (prodOpEquiv D₁ D₂).functor ≅
    E.functor ⋙ F := Iso.refl _
  rw [isRightDerivabilityStructure_iff (Φ₁.prod Φ₂).op (E.functor ⋙ L)
    (E'.functor ⋙ L') _ (isoWhiskerLeft E.functor e)]
  have : (isoWhiskerLeft E.functor e).hom = TwoSquare.vComp w.hom e.hom := by
    ext ⟨X₁, X₂⟩ <;> simp [w, L']
  rw [this]
  infer_instance

end LocalizerMorphism

end CategoryTheory
