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

variable (A) in
abbrev GrothendieckTopology.ev (S : C) : Sheaf K A ⥤ A := (sheafSections K A).obj (op S)

instance (S : C) [HasLimitsOfShape J A] : PreservesLimitsOfShape J (K.ev A S) :=
  inferInstanceAs <| PreservesLimitsOfShape _ ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj _)

variable [∀ (S : C), PreservesColimitsOfShape J (K.ev A S)]

instance : PreservesColimitsOfShape J (sheafToPresheaf K A) where
  preservesColimit {G} := {
    preserves {c} hc := by
      constructor
      apply Limits.evaluationJointlyReflectsColimits
      intro ⟨S⟩
      exact isColimitOfPreserves (K.ev A S) hc }

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

variable [∀ (S : C), PreservesFiniteColimits (K.ev A S)]

instance : PreservesFiniteColimits (sheafToPresheaf K A) where
  preservesFiniteColimits _ := ⟨inferInstance⟩

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

universe v

variable {A C J : Type*} [Category A] [Category C] [Category J]

variable [FinitaryExtensive C] [Abelian A] [HasWeakSheafify (extensiveTopology C) A]
    [HasFiniteLimits A]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (G : J ⥤ Cᵒᵖ ⥤ A)

variable [HasColimitsOfShape J A]

#check G.flip ⋙ colim

noncomputable def pointwiseColimitCone (G : J ⥤ Cᵒᵖ ⥤ A) : Cone G where
  pt := G.flip ⋙ colim
  π := {
    app X := {
      app Y := by
        simp
        change _ ⟶ (G.flip.obj Y).obj X
        sorry
      naturality := sorry
    }
    naturality := sorry
  }

lemma isSheaf_colimit [HasColimitsOfShape J A] (G : J ⥤ Sheaf (extensiveTopology C) A) :
    Presheaf.IsSheaf (extensiveTopology C) (colimit (G ⋙ sheafToPresheaf _ A)) := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
  sorry

instance (F : C ⥤ A) [Fintype J] [PreservesColimitsOfShape (Discrete J) F] :
    PreservesLimitsOfShape (Discrete J) F := sorry

-- instance (S : C) : PreservesColimitsOfShape J ((extensiveTopology C).ev A S) := sorry

-- instance : PreservesColimits (sheafToPresheaf (extensiveTopology C) A) := ⟨inferInstance⟩

instance [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (sheafToPresheaf (extensiveTopology C) A) where
      preservesColimit {G} := by
        suffices CreatesColimit G (sheafToPresheaf (extensiveTopology C) A) from inferInstance
        apply createsColimitOfIsSheaf
        intro c hc
        rw [Presheaf.isSheaf_iff_preservesFiniteProducts]
        exact {
          preserves I _ := by
            -- suffices PreservesColimitsOfShape (Discrete I) c.pt from inferInstance
            let i : c.pt ≅ colimit (G ⋙ sheafToPresheaf _ _) :=
              hc.coconePointUniqueUpToIso (colimit.isColimit _)
            suffices PreservesLimitsOfShape (Discrete I) (colimit (G ⋙ sheafToPresheaf _ _)) from
              preservesLimitsOfShape_of_natIso i.symm
            -- exact { preservesColimit {K} := {
            --     preserves {s} hs := by
            --       constructor
            --       sorry } } }
            apply ( config := {allowSynthFailures := true} ) preservesLimitsOfShape_of_discrete
            intro f
            exact {
              preserves {s} hs := by
                constructor
                sorry
                -- let b := biproduct (fun x ↦ c.pt.obj (f x))
                -- let hb := biproduct.isLimit (fun x ↦ c.pt.obj (f x))
                -- apply (isProductEquiv _ _).toFun
                -- refine IsLimit.ofIsoLimit (biproduct.isLimit _) ?_
                -- refine Cones.ext ?_ ?_
                -- · simp
                --   let i : (biproduct.bicone fun a ↦ c.pt.obj (f a)).pt ≅ sigmaObj _ :=
                --     (biproduct.isColimit _).coconePointUniqueUpToIso (colimit.isColimit _)
                --   refine i ≪≫ ?_
                --   sorry
                -- · sorry
            } }

end

end CategoryTheory
