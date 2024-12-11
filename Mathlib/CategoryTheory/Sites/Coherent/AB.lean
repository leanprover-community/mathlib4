/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveSheaves
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms
/-!

# Grothendieck axioms for the category of sheaves for the extensive topology
-/

namespace CategoryTheory

open CategoryTheory Limits Sheaf GrothendieckTopology Opposite

section

variable {C D J : Type*} [Category C] [Category D] [Category J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteLimits F] [ReflectsFiniteLimits F] [HasFiniteLimits C]
    [PreservesColimitsOfShape J F]

include F in
lemma hasExactColimitsOfShape_transfer : HasExactColimitsOfShape J C where
  preservesFiniteLimits := { preservesFiniteLimits I := { preservesLimit {G} := {
    preserves {c} hc := by
      constructor
      apply isLimitOfReflects F
      refine (IsLimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesColimitNatIso F).symm)
        ((_ ⋙ colim).mapCone c) _ ?_) (isLimitOfPreserves _ hc)
      exact Cones.ext ((preservesColimitNatIso F).symm.app _)
        fun i ↦ by erw [← (preservesColimitNatIso F).inv.naturality]; rfl } } }

end

section

variable {C D J : Type*} [Category C] [Category D] [Category J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] [HasExactLimitsOfShape J D]
    (F : C ⥤ D) [PreservesFiniteColimits F] [ReflectsFiniteColimits F] [HasFiniteColimits C]
    [PreservesLimitsOfShape J F]

include F in
lemma hasExactLimitsOfShape_transfer : HasExactLimitsOfShape J C where
  preservesFiniteColimits := { preservesFiniteColimits I := { preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply isColimitOfReflects F
      refine (IsColimit.equivOfNatIsoOfIso (isoWhiskerLeft G (preservesLimitNatIso F).symm)
        ((_ ⋙ lim).mapCocone c) _ ?_) (isColimitOfPreserves _ hc)
      refine Cocones.ext ((preservesLimitNatIso F).symm.app _) fun i ↦ ?_
      simp only [Functor.comp_obj, lim_obj, Functor.mapCocone_pt, isoWhiskerLeft_inv, Iso.symm_inv,
        Cocones.precompose_obj_pt, whiskeringRight_obj_obj, Functor.const_obj_obj,
        Cocones.precompose_obj_ι, NatTrans.comp_app, whiskerLeft_app, preservesLimitNatIso_hom_app,
        Functor.mapCocone_ι_app, Functor.comp_map, whiskeringRight_obj_map, lim_map, Iso.app_hom,
        Iso.symm_hom, preservesLimitNatIso_inv_app, Category.assoc]
      rw [← Iso.eq_inv_comp]
      erw [← (preservesLimitNatIso F).inv.naturality]
      rfl } } }

end

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
      refine Cones.ext (i.app _) ?_
      intro j
      erw [← i.hom.naturality]
      rfl } } }

variable (K : GrothendieckTopology C) [HasWeakSheafify K A]

variable [PreservesColimitsOfShape J (sheafToPresheaf K A)]

instance : HasExactColimitsOfShape J (Sheaf K A) :=
  hasExactColimitsOfShape_transfer (sheafToPresheaf K A)

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
      erw [← i.hom.naturality]
      rfl } } }

variable (K : GrothendieckTopology C) [HasWeakSheafify K A]

variable [PreservesFiniteColimits (sheafToPresheaf K A)]

instance : HasExactLimitsOfShape J (Sheaf K A) :=
  hasExactLimitsOfShape_transfer (sheafToPresheaf K A)

end

section

open Presheaf

variable {A C J : Type*} [Category A] [Category C] [Category J] (K : GrothendieckTopology C)
  [HasColimitsOfShape J A]

def createsColimitOfIsSheaf (F : J ⥤ Sheaf K A)
    (h : ∀ (c : Cocone (F ⋙ sheafToPresheaf K A)) (_ : IsColimit c), IsSheaf K c.pt) :
    CreatesColimit F (sheafToPresheaf K A) :=
  createsColimitOfReflectsIso fun E hE =>
    { liftedCocone := ⟨⟨E.pt, h _ hE⟩,
        ⟨fun _ => ⟨E.ι.app _⟩, fun _ _ _ => Sheaf.Hom.ext <| E.ι.naturality _⟩⟩
      validLift := Cocones.ext (eqToIso rfl) fun j => by simp
      makesColimit :=
        { desc := fun S => ⟨hE.desc ((sheafToPresheaf K A).mapCocone S)⟩
          fac := fun S j => by ext1; dsimp; rw [hE.fac]; rfl
          uniq := fun S m hm => by
            ext1
            exact hE.uniq ((sheafToPresheaf K A).mapCocone S) m.val fun j =>
              congr_arg Hom.val (hm j) } }

end

section

variable {A C J : Type*} [Category A] [Category C] [Category J]
  [FinitaryExtensive C] [Preadditive A] [HasColimitsOfShape J A]

@[simps]
noncomputable def pointwiseColimitCone (G : J ⥤ Cᵒᵖ ⥤ A) : Cocone G where
  pt := G.flip ⋙ colim
  ι := {
    app X := { app Y := (colimit.ι _ X : (G.flip.obj Y).obj X ⟶ _) }
    naturality X Y f := by
      ext x
      simp only [Functor.const_obj_obj, Functor.comp_obj, colim_obj, NatTrans.comp_app,
        Functor.const_obj_map, Category.comp_id]
      change (G.flip.obj x).map f ≫ _ = _
      rw [colimit.w] }

noncomputable def isColimitPointwiseColimitCone (G : J ⥤ Cᵒᵖ ⥤ A) :
    IsColimit (pointwiseColimitCone G) := by
  apply IsColimit.ofIsoColimit (combinedIsColimit _
    (fun k ↦ ⟨colimit.cocone _, colimit.isColimit _⟩))
  exact Cocones.ext (Iso.refl _)

lemma isSheaf_pointwiseColimit (G : J ⥤ Sheaf (extensiveTopology C) A) :
    Presheaf.IsSheaf (extensiveTopology C) (pointwiseColimitCone (G ⋙ sheafToPresheaf _ A)).pt := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  dsimp only [pointwiseColimitCone_pt]
  apply (config := { allowSynthFailures := true } ) comp_preservesFiniteProducts
  · have : ∀ (i : J), PreservesFiniteProducts ((G ⋙ sheafToPresheaf _ A).obj i) := by
      intro i
      rw [← Presheaf.isSheaf_iff_preservesFiniteProducts]
      exact Sheaf.cond _
    exact { preserves I := { preservesLimit {K} := {
      preserves {s} hs := by
        constructor
        apply evaluationJointlyReflectsLimits
        intro i
        obtain ⟨h⟩ := (this i).1 I
        exact ((h (K := K)).1 hs).some } } }
  · exact {
      preserves I _ := by
        apply ( config := {allowSynthFailures := true} )
          preservesProductsOfShape_of_preservesBiproductsOfShape
        apply preservesBiproductsOfShape_of_preservesCoproductsOfShape }

instance : PreservesColimitsOfShape J (sheafToPresheaf (extensiveTopology C) A) where
  preservesColimit {G} := by
    suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
    apply createsColimitOfIsSheaf
    intro c hc
    let i : c.pt ≅ (G ⋙ sheafToPresheaf _ _).flip ⋙ colim :=
      hc.coconePointUniqueUpToIso (isColimitPointwiseColimitCone _)
    rw [Presheaf.isSheaf_of_iso_iff i]
    exact isSheaf_pointwiseColimit _

instance [HasFiniteColimits A] :
    PreservesFiniteColimits (sheafToPresheaf (extensiveTopology C) A) where
  preservesFiniteColimits _ := inferInstance

example [HasExactColimitsOfShape J A] [HasWeakSheafify (extensiveTopology C) A]
    [HasFiniteLimits A] : HasExactColimitsOfShape J (Sheaf (extensiveTopology C) A) := inferInstance

example [HasLimitsOfShape J A] [HasExactLimitsOfShape J A]
  [HasWeakSheafify (extensiveTopology C) A] [HasFiniteColimits A] :
  HasExactLimitsOfShape J (Sheaf (extensiveTopology C) A) := inferInstance

end

end CategoryTheory
