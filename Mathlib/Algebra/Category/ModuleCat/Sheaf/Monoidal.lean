/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.OfCommRing
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Monoidal structure on sheaves of modules

The symmetric monoidal structure is obtained by localizing the tensor product of presheaves
of modules along the morphisms inverted by sheafification.
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory BraidedCategory Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

section

variable {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} [LocallySmall.{w} C]
  (hP : P.IsConservativeFamilyOfPoints)
  (R₀ : Cᵒᵖ ⥤ CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]

include hP

lemma isMonoidal_presheafOfModulesW :
    (J.W.inverseImage (PresheafOfModulesOfCommRing.toPresheaf R₀)).IsMonoidal := sorry

end

instance (R₀ : Cᵒᵖ ⥤ CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [GrothendieckTopology.HasEnoughPoints.{w} J] [LocallySmall.{w} C] :
    (J.W.inverseImage (PresheafOfModulesOfCommRing.toPresheaf R₀)).IsMonoidal := by
  obtain ⟨P, _, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
  exact hP.isMonoidal_presheafOfModulesW _

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

namespace SheafOfModulesOfCommRing

open PresheafOfModulesOfCommRing

variable [HasWeakSheafify J AddCommGrpCat.{w}] (R : Sheaf J CommRingCat.{w})

--MOVE
/-- Morphisms of presheaves of modules inverted by sheafification. -/
abbrev W : MorphismProperty (PresheafOfModulesOfCommRing.{w} R.obj) :=
  J.W.inverseImage (toPresheaf R.obj)

example [LocallySmall.{w} C] [GrothendieckTopology.HasEnoughPoints.{w} J] :
    (W R).IsMonoidal := inferInstance

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat)]
-- MOVE
omit [HasWeakSheafify J AddCommGrpCat.{w}] in
@[simp]
lemma W_forget_map_iff_isIso {F G : SheafOfModulesOfCommRing.{w} R} (f : F ⟶ G) :
    W R ((forget R).map f) ↔ IsIso f := by
  change J.W ((sheafToPresheaf J AddCommGrpCat).map ((SheafOfModules.toSheaf _).map f)) ↔ _
  rw [J.W_sheafToPresheaf_map_iff_isIso, isIso_iff_of_reflects_iso]

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
-- MOVE
lemma W_iff_isIso_map_sheafification
    {F G : PresheafOfModulesOfCommRing.{w} R.obj} (f : F ⟶ G) :
    W R f ↔ IsIso ((sheafification R).map f) := by
  change J.W ((toPresheaf R.obj).map f) ↔ _
  rw [J.W_iff, ← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rfl

variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat)] [(W R).IsMonoidal]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance monoidalCategory :
    MonoidalCategory (SheafOfModulesOfCommRing.{w} R) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (sheafification R) (W R) (unit := unit R)
    (asIso ((sheafificationAdjunction.{w} R).counit.app (unit R)))))

set_option backward.isDefEq.respectTransparency false in
noncomputable instance symmetricCategory :
    SymmetricCategory (SheafOfModulesOfCommRing.{w} R) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (sheafification R) (W R) (unit := unit R)
    (asIso ((sheafificationAdjunction.{w} R).counit.app (unit R)))))

set_option backward.isDefEq.respectTransparency false in
noncomputable instance monoidalSheafification :
    (sheafification.{w} R).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (sheafification R) _ _).Monoidal

noncomputable instance : (forget.{w} R).LaxMonoidal :=
  (sheafificationAdjunction R).rightAdjointLaxMonoidal

example : (sheafificationAdjunction R).IsMonoidal := by
  infer_instance

omit [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat)] in
lemma W_μ (F G : SheafOfModulesOfCommRing.{w} R) :
    W R (Functor.LaxMonoidal.μ (forget R) F G) := by
  rw [W_iff_isIso_map_sheafification]
  let adj := sheafificationAdjunction R
  have : IsIso ((sheafification R).map (Functor.LaxMonoidal.μ (forget R) F G) ≫
      adj.counit.app (F ⊗ G)) := by
    rw [adj.map_μ_comp_counit_app_tensor]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (F ⊗ G))

section

variable (F : SheafOfModulesOfCommRing.{w} R)

set_option backward.isDefEq.respectTransparency false in
instance : PreservesColimitsOfSize.{w, w} (tensorLeft F) := by
  let adj := sheafificationAdjunction.{w} R
  have := adj.fullyFaithfulROfIsIsoCounit.faithful
  have := adj.fullyFaithfulROfIsIsoCounit.full
  rw [adj.preservesColimitsOfSize_iff (H := tensorLeft F)]
  apply preservesColimits_of_natIso
    ((Functor.Monoidal.commTensorLeft (sheafification R) _).symm ≪≫
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
      (asIso (adj.counit.app F))))

instance : PreservesColimitsOfSize.{w, w} (tensorRight F) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)

instance : PreservesFiniteColimits (tensorLeft F) :=
  PreservesColimitsOfSize.preservesFiniteColimits (tensorLeft F)

instance : PreservesFiniteColimits (tensorRight F) :=
  PreservesColimitsOfSize.preservesFiniteColimits (tensorRight F)

instance : (tensorLeft F).Additive := sorry

instance : (tensorRight F).Additive := sorry

end

instance : MonoidalPreadditive (SheafOfModulesOfCommRing.{w} R) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} _ _ := (tensorLeft X).map_add
  add_whiskerRight {X _ _} _ _ := (tensorRight X).map_add

end SheafOfModulesOfCommRing
