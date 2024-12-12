/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
/-!

# AB axioms in functor categories
-/

namespace CategoryTheory

open CategoryTheory Limits Opposite

section

variable {A C J : Type*} [Category A] [Category C] [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] [HasFiniteLimits A]

instance : HasExactColimitsOfShape J (C ⥤ A) where
  preservesFiniteLimits := { preservesFiniteLimits I := { preservesLimit {K} := {
    preserves {c} hc := by
      constructor
      apply Limits.evaluationJointlyReflectsLimits
      intro k
      let F : (J ⥤ C ⥤ A) ⥤ (J ⥤ A) :=
        (whiskeringRight J (C ⥤ A) A).obj <| (evaluation C A).obj k
      let i : F ⋙ colim ≅ colim ⋙ (evaluation C A).obj k :=
        (preservesColimitNatIso ((evaluation C A).obj k)).symm
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft K i) ((F ⋙ colim).mapCone c) _ ?_)
        (isLimitOfPreserves _ hc)
      exact Cones.ext (i.app _) (fun _ ↦ i.hom.naturality _) } } }

end

section

variable {A C J : Type*} [Category A] [Category C] [Category J]
    [HasLimitsOfShape J A] [HasExactLimitsOfShape J A] [HasFiniteColimits A]

instance : HasExactLimitsOfShape J (C ⥤ A) where
  preservesFiniteColimits := { preservesFiniteColimits I := { preservesColimit {K} := {
    preserves {c} hc := by
      constructor
      apply Limits.evaluationJointlyReflectsColimits
      intro k
      let F : (J ⥤ C ⥤ A) ⥤ (J ⥤ A) :=
        (whiskeringRight J (C ⥤ A) A).obj <| (evaluation C A).obj k
      let i  : F ⋙ lim ≅ lim ⋙ (evaluation C A).obj k :=
        (preservesLimitNatIso ((evaluation C A).obj k)).symm
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft K i) ((F ⋙ lim).mapCocone c) _ ?_)
        (isColimitOfPreserves _ hc)
      refine Cocones.ext (i.app _) ?_
      intro j
      simp only [Functor.comp_obj, lim_obj, evaluation_obj_obj, Functor.mapCocone_pt,
        isoWhiskerLeft_inv, Iso.symm_inv, Cocones.precompose_obj_pt, Functor.const_obj_obj,
        Cocones.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, lim_map, Iso.app_hom, Iso.symm_hom,
        preservesLimitNatIso_inv_app, Category.assoc, evaluation_obj_map, i]
      rw [← Iso.eq_inv_comp]
      exact i.hom.naturality _ } } }

end

end CategoryTheory
