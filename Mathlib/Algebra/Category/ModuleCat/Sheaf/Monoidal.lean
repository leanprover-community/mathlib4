/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctorMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Point
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Monoidal structure on sheaves of modules

-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

section

variable {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} [LocallySmall.{w} C]
  (hP : P.IsConservativeFamilyOfPoints)
  (R₀ : Cᵒᵖ ⥤ CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]

include hP

lemma presheafOfModulesW_iff {F G : PresheafOfModules.{w} (R₀ ⋙ forget₂ _ _)} (f : F ⟶ G) :
    J.W ((PresheafOfModules.toPresheaf _).map f) ↔
      ∀ (Φ : P.FullSubcategory), IsIso ((Φ.obj.presheafOfModulesFiber _).map f) := by
  rw [hP.W_iff]
  refine forall_congr' (fun Φ ↦ ?_)
  simp only [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{w} (Φ.obj.presheafFiber.obj R₀ :)) AddCommGrpCat)]
  rfl

lemma isMonoidal_presheafOfModulesW :
    (J.W.inverseImage (PresheafOfModules.toPresheaf (R₀ ⋙ forget₂ _ _))).IsMonoidal :=
  .mk' _ (fun f g hf hg ↦ by
    simp only [MorphismProperty.inverseImage_iff, hP.presheafOfModulesW_iff] at hf hg ⊢
    intro Φ
    rw [Functor.Monoidal.map_tensor]
    infer_instance)

end

instance (R₀ : Cᵒᵖ ⥤ CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [GrothendieckTopology.HasEnoughPoints.{w} J] [LocallySmall.{w} C] :
    (J.W.inverseImage (PresheafOfModules.toPresheaf (R₀ ⋙ forget₂ _ _))).IsMonoidal := by
  obtain ⟨P, _, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
  exact hP.isMonoidal_presheafOfModulesW _

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

namespace SheafOfModules

variable [HasWeakSheafify J AddCommGrpCat.{w}] (R : Sheaf J CommRingCat.{w})

abbrev W : MorphismProperty (PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _)) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf _)

example [LocallySmall.{w} C] [GrothendieckTopology.HasEnoughPoints.{w} J] :
    (W R).IsMonoidal := inferInstance

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat)]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat)]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance monoidalCategory [(W R).IsMonoidal] :
    MonoidalCategory (SheafOfModules ((sheafCompose J (forget₂ _ _)).obj R)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (PresheafOfModules.sheafification.{w} (J := J) (R₀ := R.obj ⋙ forget₂ _ _)
      (R := ((sheafCompose J (forget₂ _ _)).obj R)) (𝟙 _)) (W R) (unit := unit _)
        (asIso (((PresheafOfModules.sheafificationAdjunction.{w} (J := J)
          (R₀ := R.obj ⋙ forget₂ _ _) (R := ((sheafCompose J (forget₂ _ _)).obj R)))
            (𝟙 _)).counit.app (unit _)) :)))

set_option backward.isDefEq.respectTransparency false in
noncomputable instance [(W R).IsMonoidal] :
  (PresheafOfModules.sheafification.{w} (J := J) (R₀ := R.obj ⋙ forget₂ _ _)
    (R := ((sheafCompose J (forget₂ _ _)).obj R)) (𝟙 _)).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafification.{w} (J := J) (R₀ := R.obj ⋙ forget₂ _ _)
      (R := ((sheafCompose J (forget₂ _ _)).obj R)) (𝟙 _)) (W R) (unit := unit _)
        (asIso (((PresheafOfModules.sheafificationAdjunction.{w} (J := J)
          (R₀ := R.obj ⋙ forget₂ _ _) (R := ((sheafCompose J (forget₂ _ _)).obj R)))
            (𝟙 _)).counit.app (unit _)) :)).Monoidal


end SheafOfModules
