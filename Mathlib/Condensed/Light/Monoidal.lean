/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import Mathlib.CategoryTheory.Monoidal.Closed.Transport
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Condensed.Light.CartesianClosed
import Mathlib.Condensed.Light.Module
import Mathlib.Condensed.Light.Small

/-!

# Closed symmetric monoidal structure on light condensed modules

We define a symmetric monoidal structure on a category of sheaves on a small site that is equivalent
to light condensed modules, by localizing the symmetric monoidal structure on the presheaf category.

By Day's reflection theorem, we obtain a closed structure.

Finally, we transfer all this structure along the equivalence of categories, to obtain the closed
symmetric monoidal structure on light condensed modules.
-/

universe u

noncomputable section

open CategoryTheory Monoidal Sheaf MonoidalCategory MonoidalClosed MonoidalClosed.FunctorCategory

namespace LightCondensed

attribute [local instance] monoidalCategory symmetricCategory

variable (R : Type (u + 1)) [CommRing R]

variable (R : Type u) [CommRing R]

instance : MonoidalCategory (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalCategory (Transported (equivSmall (ModuleCat R)).symm))

instance : SymmetricCategory (LightCondMod.{u} R) :=
  inferInstanceAs (SymmetricCategory (Transported (equivSmall (ModuleCat R)).symm))

/--
The category of sheaves on a small site that is equivalent to light condensed modules is monoidal
closed.
-/
local instance : MonoidalClosed
    (Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) (ModuleCat R)) :=
  Reflective.monoidalClosed (sheafificationAdjunction _ _)

instance : MonoidalClosed (LightCondMod.{u} R) :=
  inferInstanceAs (MonoidalClosed (Transported (equivSmall (ModuleCat R)).symm))

section

variable {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C}
    {A : Type*} [Category A]
    {F G : D ⥤ Sheaf J A} (i : F ⋙ sheafToPresheaf _ _ ≅ G ⋙ sheafToPresheaf _ _)

def _root_.CategoryTheory.Sheaf.natIsoCancel : F ≅ G :=
  NatIso.ofComponents (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso (i.app _)) (by
    intro X Y f
    apply (sheafToPresheaf _ _).map_injective
    simpa [-sheafToPresheaf_map, -sheafToPresheaf_obj] using i.hom.naturality _)

end

section

variable {C D E : Type*} [Category C] [Category D] [Category E]
    (e : C ≌ D) [MonoidalCategory C] [MonoidalCategory E] (F : Transported e ⥤ E)
    (G : E ⥤ Transported e)

def _root_.CategoryTheory.Equivalence.monoidalOfComp [(e.functor ⋙ F).Monoidal] : F.Monoidal :=
  Functor.Monoidal.transport (e.invFunIdAssoc F)

def _root_.CategoryTheory.Equivalence.monoidalOfComp' [(G ⋙ e.inverse).Monoidal] : G.Monoidal :=
  letI : (G ⋙ (equivalenceTransported e).inverse ⋙ (equivalenceTransported e).functor).Monoidal :=
    inferInstanceAs
      ((G ⋙ (equivalenceTransported e).inverse) ⋙ (equivalenceTransported e).functor).Monoidal
  Functor.Monoidal.transport (Functor.isoWhiskerLeft G e.counitIso ≪≫ G.rightUnitor)

end

attribute [local instance] monoidalCategory in
def monoidalOfPostcomp {E : Type*} [Category E] [MonoidalCategory E] (F : E ⥤ LightCondMod.{u} R)
    [(F ⋙ (equivSmall _).functor).Monoidal] : F.Monoidal :=
  letI : (F ⋙ (equivSmall _).symm.inverse).Monoidal :=
    inferInstanceAs (F ⋙ (equivSmall _).functor).Monoidal
  (equivSmall (ModuleCat R)).symm.monoidalOfComp' F


def monoidalOfPrecomp {E : Type*} [Category E] [MonoidalCategory E] (F : LightCondSet.{u} ⥤ E)
    [((equivSmall _).inverse ⋙ F).Monoidal] : F.Monoidal :=
  letI : ((equivSmall _).symm.functor ⋙ F).Monoidal :=
    inferInstanceAs ((equivSmall _).inverse ⋙ F).Monoidal
  letI : (equivSmall (Type u)).symm.inverse.Monoidal :=
    ((Functor.Monoidal.nonempty_monoidal_iff_preservesFiniteProducts
      (equivSmall (Type u)).symm.inverse).mpr inferInstance).some
  Functor.Monoidal.transport ((equivSmall _).symm.invFunIdAssoc F)

open Functor

instance : (free R).Monoidal := by
  letI : MonoidalCategory (Sheaf
      ((equivSmallModel _).inverse.inducedTopology (coherentTopology LightProfinite.{u}))
      (ModuleCat.{u} R)) := monoidalCategory _ _
  apply (config := {allowSynthFailures := true}) monoidalOfPostcomp
  apply (config := {allowSynthFailures := true}) monoidalOfPrecomp
  let i : (equivSmall (Type u)).inverse ⋙ free R ⋙ (equivSmall (ModuleCat R)).functor ≅
      Sheaf.composeAndSheafify _ (ModuleCat.free R) := by
    refine natIsoCancel ?_
    let j := (((equivSmallModel LightProfinite.{u}).transportSheafificationAdjunction
            (coherentTopology LightProfinite.{u})
            ((equivSmallModel _).inverse.inducedTopology (coherentTopology LightProfinite.{u}))
            (ModuleCat.{u} R)).leftAdjointUniq
            (sheafificationAdjunction (coherentTopology LightProfinite.{u}) _)).symm
    calc _ ≅ ((equivSmall (Type u)).inverse ⋙
      (sheafToPresheaf (coherentTopology LightProfinite.{u}) (Type u) ⋙
        (whiskeringRight LightProfinite.{u}ᵒᵖ (Type u) (ModuleCat.{u} R)).obj (ModuleCat.free R) ⋙
          (Equivalence.transportAndSheafify (coherentTopology LightProfinite)
            ((equivSmallModel LightProfinite).inverse.inducedTopology
              (coherentTopology LightProfinite))
            (equivSmallModel LightProfinite) (ModuleCat R))) ⋙
            (equivSmall (ModuleCat.{u} R)).functor) ⋙
              sheafToPresheaf ((equivSmallModel LightProfinite.{u}).inverse.inducedTopology
                (coherentTopology LightProfinite.{u})) (ModuleCat.{u} R) := ?_
      _ ≅ _ := ?_
    · exact isoWhiskerRight (isoWhiskerLeft _ (isoWhiskerRight (isoWhiskerLeft _
        (isoWhiskerLeft _ j)) _)) _
    · refine Functor.associator _ _ _ ≪≫ ?_
      refine isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ ?_
      refine isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫ ?_
      refine isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.associator _ _ _)) ≪≫ ?_
      refine isoWhiskerLeft _ (isoWhiskerLeft _ (isoWhiskerLeft _ (Functor.associator _ _ _))) ≪≫ ?_
      refine isoWhiskerLeft _ (isoWhiskerLeft _ (isoWhiskerLeft _
        (isoWhiskerLeft _ (Functor.associator _ _ _)))) ≪≫ ?_
      refine ?_ ≪≫ (Functor.associator _ _ _).symm
      refine ?_ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm
      refine isoWhiskerLeft (equivSmall (Type u)).inverse
        (isoWhiskerLeft (sheafToPresheaf (coherentTopology LightProfinite) (Type u)) (isoWhiskerLeft
          ((whiskeringRight LightProfiniteᵒᵖ (Type u) (ModuleCat R)).obj (ModuleCat.free R))
            (isoWhiskerLeft (equivSmallModel LightProfinite).op.congrLeft.functor
              (isoWhiskerLeft (H := sheafToPresheaf
                ((equivSmallModel LightProfinite.{u}).inverse.inducedTopology
                  (coherentTopology LightProfinite.{u})) (ModuleCat.{u} R)) (presheafToSheaf
                    ((equivSmallModel LightProfinite.{u}).inverse.inducedTopology
                      (coherentTopology LightProfinite.{u}))
                        (ModuleCat.{u} R)) ?_)))) ≪≫ ?_
      · refine NatIso.ofComponents (fun X ↦ ?_) ?_
        · exact isoWhiskerRight (equivSmallModel LightProfinite.{u}).op.counitIso X.val ≪≫
              Functor.leftUnitor _
        · intros
          ext
          simp [Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
            Equivalence.sheafCongr.inverse]
      · refine ?_ ≪≫ (Functor.associator _ _ _)
        refine (Functor.associator _ _ _).symm ≪≫ ?_
        refine (Functor.associator _ _ _).symm ≪≫ ?_
        refine (Functor.associator _ _ _).symm ≪≫ ?_
        refine isoWhiskerRight ?_ _
        refine NatIso.ofComponents (fun X ↦ ?_) ?_
        · exact (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
            (isoWhiskerRight (equivSmallModel LightProfinite.{u}).op.counitIso X.val ≪≫
              Functor.leftUnitor _) (ModuleCat.free R)
        · intros
          apply NatTrans.ext
          apply funext
          intro
          simp only [Equivalence.sheafCongr, Equivalence.sheafCongr.functor,
            Equivalence.sheafCongr.inverse, Equivalence.congrLeft_functor, Equivalence.op_inverse,
            Functor.comp_obj, sheafToPresheaf_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_obj,
            Functor.op_obj, Functor.comp_map, sheafToPresheaf_map, whiskeringRight_obj_map,
            whiskeringLeft_obj_map, Equivalence.op_functor, Equivalence.op_counitIso,
            isoWhiskerRight_trans, isoWhiskerRight_twice, Iso.trans_assoc, Iso.trans_hom,
            Iso.symm_hom, isoWhiskerRight_hom, NatIso.op_inv, NatTrans.comp_app,
            Functor.whiskerLeft_app, Functor.whiskerRight_app,
            Functor.associator_inv_app, Functor.associator_hom_app, Functor.id_obj, NatTrans.op_app,
            Functor.leftUnitor_hom_app, CategoryTheory.Functor.map_id, Category.comp_id,
            Category.id_comp, Category.assoc]
          simp [← Functor.map_comp]
  exact Functor.Monoidal.transport i.symm

end LightCondensed
