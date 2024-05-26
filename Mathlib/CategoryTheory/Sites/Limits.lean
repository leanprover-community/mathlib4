/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

#align_import category_theory.sites.limits from "leanprover-community/mathlib"@"95e83ced9542828815f53a1096a4d373c1b08a77"

/-!

# Limits and colimits of sheaves

## Limits

We prove that the forgetful functor from `Sheaf J D` to presheaves creates limits.
If the target category `D` has limits (of a certain shape),
this then implies that `Sheaf J D` has limits of the same shape and that the forgetful
functor preserves these limits.

## Colimits

Given a diagram `F : K ⥤ Sheaf J D` of sheaves, and a colimit cocone on the level of presheaves,
we show that the cocone obtained by sheafifying the cocone point is a colimit cocone of sheaves.

This allows us to show that `Sheaf J D` has colimits (of a certain shape) as soon as `D` does.

-/


namespace CategoryTheory

namespace Sheaf

open CategoryTheory.Limits

open Opposite

universe w w' v u z z' u₁ u₂

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {D : Type w} [Category.{w'} D]
variable {K : Type z} [Category.{z'} K]

section Limits

noncomputable section

section

/-- An auxiliary definition to be used below.

Whenever `E` is a cone of shape `K` of sheaves, and `S` is the multifork associated to a
covering `W` of an object `X`, with respect to the cone point `E.X`, this provides a cone of
shape `K` of objects in `D`, with cone point `S.X`.

See `isLimitMultiforkOfIsLimit` for more on how this definition is used.
-/
def multiforkEvaluationCone (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D)) (X : C)
    (W : J.Cover X) (S : Multifork (W.index E.pt)) :
    Cone (F ⋙ sheafToPresheaf J D ⋙ (evaluation Cᵒᵖ D).obj (op X)) where
  pt := S.pt
  π :=
    { app := fun k => (Presheaf.isLimitOfIsSheaf J (F.obj k).1 W (F.obj k).2).lift <|
        Multifork.ofι _ S.pt (fun i => S.ι i ≫ (E.π.app k).app (op i.Y))
          (by
            intro i
            simp only [Category.assoc]
            erw [← (E.π.app k).naturality, ← (E.π.app k).naturality]
            dsimp
            simp only [← Category.assoc]
            congr 1
            apply S.condition)
      naturality := by
        intro i j f
        dsimp [Presheaf.isLimitOfIsSheaf]
        rw [Category.id_comp]
        apply Presheaf.IsSheaf.hom_ext (F.obj j).2 W
        intro ii
        rw [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← (F.map f).val.naturality, ←
          Category.assoc, Presheaf.IsSheaf.amalgamate_map]
        dsimp [Multifork.ofι]
        erw [Category.assoc, ← E.w f]
        aesop_cat }
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.multifork_evaluation_cone CategoryTheory.Sheaf.multiforkEvaluationCone

variable [HasLimitsOfShape K D]

/-- If `E` is a cone of shape `K` of sheaves, which is a limit on the level of presheaves,
this definition shows that the limit presheaf satisfies the multifork variant of the sheaf
condition, at a given covering `W`.

This is used below in `isSheaf_of_isLimit` to show that the limit presheaf is indeed a sheaf.
-/
def isLimitMultiforkOfIsLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) (X : C) (W : J.Cover X) : IsLimit (W.multifork E.pt) :=
  Multifork.IsLimit.mk _
    (fun S => (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).lift <|
      multiforkEvaluationCone F E X W S)
    (by
      intro S i
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op i.Y)) hE).hom_ext
      intro k
      dsimp [Multifork.ofι]
      erw [Category.assoc, (E.π.app k).naturality]
      dsimp
      rw [← Category.assoc]
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac
        (multiforkEvaluationCone F E X W S)]
      dsimp [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      erw [Presheaf.IsSheaf.amalgamate_map]
      rfl)
    (by
      intro S m hm
      apply (isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).hom_ext
      intro k
      dsimp
      erw [(isLimitOfPreserves ((evaluation Cᵒᵖ D).obj (op X)) hE).fac]
      apply Presheaf.IsSheaf.hom_ext (F.obj k).2 W
      intro i
      dsimp only [multiforkEvaluationCone, Presheaf.isLimitOfIsSheaf]
      rw [(F.obj k).cond.amalgamate_map]
      dsimp [Multifork.ofι]
      change _ = S.ι i ≫ _
      erw [← hm, Category.assoc, ← (E.π.app k).naturality, Category.assoc]
      rfl)
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_limit_multifork_of_is_limit CategoryTheory.Sheaf.isLimitMultiforkOfIsLimit

/-- If `E` is a cone which is a limit on the level of presheaves,
then the limit presheaf is again a sheaf.

This is used to show that the forgetful functor from sheaves to presheaves creates limits.
-/
theorem isSheaf_of_isLimit (F : K ⥤ Sheaf J D) (E : Cone (F ⋙ sheafToPresheaf J D))
    (hE : IsLimit E) : Presheaf.IsSheaf J E.pt := by
  rw [Presheaf.isSheaf_iff_multifork]
  intro X S
  exact ⟨isLimitMultiforkOfIsLimit _ _ hE _ _⟩
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_sheaf_of_is_limit CategoryTheory.Sheaf.isSheaf_of_isLimit

instance (F : K ⥤ Sheaf J D) : CreatesLimit F (sheafToPresheaf J D) :=
  createsLimitOfReflectsIso fun E hE =>
    { liftedCone := ⟨⟨E.pt, isSheaf_of_isLimit _ _ hE⟩,
        ⟨fun t => ⟨E.π.app _⟩, fun u v e => Sheaf.Hom.ext _ _ <| E.π.naturality _⟩⟩
      validLift := Cones.ext (eqToIso rfl) fun j => by
        dsimp
        simp
      makesLimit :=
        { lift := fun S => ⟨hE.lift ((sheafToPresheaf J D).mapCone S)⟩
          fac := fun S j => by
            ext1
            apply hE.fac ((sheafToPresheaf J D).mapCone S) j
          uniq := fun S m hm => by
            ext1
            exact hE.uniq ((sheafToPresheaf J D).mapCone S) m.val fun j =>
              congr_arg Hom.val (hm j) } }

instance createsLimitsOfShape : CreatesLimitsOfShape K (sheafToPresheaf J D) where

instance : HasLimitsOfShape K (Sheaf J D) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J D)

instance [HasFiniteProducts D] : HasFiniteProducts (Sheaf J D) :=
  ⟨inferInstance⟩

instance [HasFiniteLimits D] : HasFiniteLimits (Sheaf J D) :=
  ⟨fun _ ↦ inferInstance⟩

end

instance createsLimits [HasLimitsOfSize.{u₁, u₂} D] :
    CreatesLimitsOfSize.{u₁, u₂} (sheafToPresheaf J D) :=
  ⟨createsLimitsOfShape⟩

instance hasLimitsOfSize [HasLimitsOfSize.{u₁, u₂} D] : HasLimitsOfSize.{u₁, u₂} (Sheaf J D) :=
  hasLimits_of_hasLimits_createsLimits (sheafToPresheaf J D)

variable {D : Type w} [Category.{max v u} D]

example [HasLimits D] : HasLimits (Sheaf J D) := inferInstance

end

end Limits

section Colimits

variable [HasWeakSheafify J D]

/-- Construct a cocone by sheafifying a cocone point of a cocone `E` of presheaves
over a functor which factors through sheaves.
In `isColimitSheafifyCocone`, we show that this is a colimit cocone when `E` is a colimit. -/
noncomputable def sheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) : Cocone F :=
  (Cocones.precompose
    (isoWhiskerLeft F (asIso (sheafificationAdjunction J D).counit).symm).hom).obj
    ((presheafToSheaf J D).mapCocone E)
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.sheafify_cocone CategoryTheory.Sheaf.sheafifyCocone

/-- If `E` is a colimit cocone of presheaves, over a diagram factoring through sheaves,
then `sheafifyCocone E` is a colimit cocone. -/
noncomputable def isColimitSheafifyCocone {F : K ⥤ Sheaf J D}
    (E : Cocone (F ⋙ sheafToPresheaf J D)) (hE : IsColimit E) : IsColimit (sheafifyCocone E) :=
  (IsColimit.precomposeHomEquiv _ ((presheafToSheaf J D).mapCocone E)).symm
    (isColimitOfPreserves _ hE)
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_colimit_sheafify_cocone CategoryTheory.Sheaf.isColimitSheafifyCocone

instance [HasColimitsOfShape K D] : HasColimitsOfShape K (Sheaf J D) :=
  ⟨fun _ => HasColimit.mk
    ⟨sheafifyCocone (colimit.cocone _), isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩

instance [HasFiniteCoproducts D] : HasFiniteCoproducts (Sheaf J D) :=
  ⟨inferInstance⟩

instance [HasFiniteColimits D] : HasFiniteColimits (Sheaf J D) :=
  ⟨fun _ ↦ inferInstance⟩

instance [HasColimitsOfSize.{u₁, u₂} D] : HasColimitsOfSize.{u₁, u₂} (Sheaf J D) :=
  ⟨inferInstance⟩

variable {D : Type w} [Category.{max v u} D]

example [HasLimits D] : HasLimits (Sheaf J D) := inferInstance

end Colimits

end Sheaf

end CategoryTheory
