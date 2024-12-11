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
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
/-!

# Grothendieck axioms for the category of sheaves for the extensive topology
-/

namespace CategoryTheory

open CategoryTheory Limits Sheaf GrothendieckTopology Opposite


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
