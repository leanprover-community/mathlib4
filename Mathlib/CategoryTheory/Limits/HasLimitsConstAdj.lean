--import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic

namespace CategoryTheory

open Category

namespace Functor

variable {C₁ C₂ : Type _} [Category C₁] [Category C₂] (L : C₁ ⥤ C₂) (J : Type _) [Category J]

@[simps!]
def compConstIso : L ⋙ Functor.const J ≅ Functor.const J ⋙ (whiskeringRight J C₁ C₂).obj L :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun j => Iso.refl _) (by aesop_cat)) (by aesop_cat)

end Functor

namespace Adjunction

-- extension of adjunction to transformation of functors
-- this should be moved...

variable {C₁ C₂ D₁ D₂ : Type _} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
  {G₁ : C₁ ⥤ D₁} {F₁ : D₁ ⥤ C₁} {G₂ : C₂ ⥤ D₂} {F₂ : D₂ ⥤ C₂}
  (adj₁ : G₁ ⊣ F₁) (adj₂ : G₂ ⊣ F₂)
  {L : C₁ ⥤ C₂} {L' : D₁ ⥤ D₂}

@[simps! apply_app symm_apply_app]
def natTransHomEquiv : (L ⋙ G₂ ⟶ G₁ ⋙ L') ≃ (F₁ ⋙ L ⟶ L' ⋙ F₂) where
  toFun τ := whiskerLeft (F₁ ⋙ L) adj₂.unit ≫ whiskerLeft F₁ (whiskerRight τ F₂) ≫
    whiskerRight adj₁.counit (L' ⋙ F₂)
  invFun τ' := whiskerRight adj₁.unit (L ⋙ G₂) ≫ whiskerLeft G₁ (whiskerRight τ' G₂) ≫
    whiskerLeft (G₁ ⋙ L') adj₂.counit
  left_inv τ := by
    ext X
    dsimp
    simp only [Functor.map_comp, assoc, counit_naturality, Functor.comp_obj, Functor.id_obj,
      counit_naturality_assoc, left_triangle_components_assoc]
    erw [τ.naturality_assoc]
    dsimp
    simp only [← L'.map_comp, left_triangle_components, Functor.map_id, comp_id]
  right_inv τ' := by
    ext X
    dsimp
    simp only [Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
    erw [← τ'.naturality]
    dsimp
    simp only [← L.map_comp_assoc, right_triangle_components, Functor.map_id, id_comp]

end Adjunction

namespace Limits

variable {C J : Type _} [Category C] [Category J]

section

variable {F : (J ⥤ C) ⥤ C} (adj : Functor.const J ⊣ F)

@[simps]
def coneOfConstAdjunction (X : J ⥤ C) : Cone X where
  pt := F.obj X
  π := adj.counit.app X

def isLimitConeOfConstAdjunction (X : J ⥤ C) : IsLimit (coneOfConstAdjunction adj X) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have eq := NatTrans.congr_app (adj.counit.naturality s.π) j
    have eq' := NatTrans.congr_app (@Adjunction.left_triangle_components _ _ _ _ _ _ adj s.pt) j
    dsimp at eq eq' ⊢
    simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, assoc, eq,
      reassoc_of% eq']
  uniq s m hm := by
    dsimp
    symm
    rw [adj.homEquiv_apply_eq]
    ext j
    simp only [Adjunction.homEquiv_counit, Functor.id_obj, NatTrans.comp_app,
      Functor.const_obj_obj, Functor.const_map_app, ← hm, coneOfConstAdjunction_π]

@[simps cone]
def limitConeOfConstAdjunction (X : J ⥤ C) : LimitCone X :=
  ⟨_, isLimitConeOfConstAdjunction adj X⟩

lemma hasLimitsOfShape_of_const_adjunction : HasLimitsOfShape J C :=
  ⟨fun X => ⟨⟨limitConeOfConstAdjunction adj X⟩⟩⟩

instance hasLimitsOfShape_of_isLeftAdjoint_const [IsLeftAdjoint (Functor.const J : C ⥤ _)] :
    HasLimitsOfShape J C :=
  hasLimitsOfShape_of_const_adjunction (Adjunction.ofLeftAdjoint _)

noncomputable def isLimitOfIsIsoConstAdjunctionHomEquivApply {X : J ⥤ C} (c : Cone X)
    (h : IsIso ((adj.homEquiv _ _) c.π)) : IsLimit c := by
  refine' IsLimit.ofIsoLimit (isLimitConeOfConstAdjunction adj X) (Iso.symm _)
  refine' Cones.ext (asIso ((adj.homEquiv _ _) c.π)) (fun j => _)
  dsimp
  simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, assoc]
  have eq := NatTrans.congr_app (adj.counit.naturality c.π) j
  have eq' := NatTrans.congr_app (@Adjunction.left_triangle_components _ _ _ _ _ _ adj c.pt) j
  dsimp at eq eq'
  rw [eq, reassoc_of% eq']

end

section

variable {C₁ C₂ J : Type _} [Category C₁] [Category C₂] [Category J]
  {F₁ : (J ⥤ C₁) ⥤ C₁} {F₂ : (J ⥤ C₂) ⥤ C₂} (adj₁ : Functor.const J ⊣ F₁)
  (adj₂ : Functor.const J ⊣ F₂) (L : C₁ ⥤ C₂)

@[simps!]
def limitComparisonOfConstAdjunction : F₁ ⋙ L ⟶ (whiskeringRight J _ _).obj L ⋙ F₂ :=
  Adjunction.natTransHomEquiv adj₁ adj₂ (L.compConstIso J).hom

noncomputable def preservesLimit_of_const_adjunction (X : J ⥤ C₁)
  [hX : IsIso ((limitComparisonOfConstAdjunction adj₁ adj₂ L).app X)] :
    PreservesLimit X L := by
  refine' preservesLimitOfPreservesLimitCone (isLimitConeOfConstAdjunction adj₁ X) _
  refine' isLimitOfIsIsoConstAdjunctionHomEquivApply adj₂ _ _
  convert hX
  dsimp
  simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj, ← F₂.map_comp]
  congr 2
  aesop_cat

noncomputable def preservesLimitsOfShape_of_const_adjunction
    [IsIso (limitComparisonOfConstAdjunction adj₁ adj₂ L)] :
    PreservesLimitsOfShape J L :=
  ⟨fun {X} => preservesLimit_of_const_adjunction adj₁ adj₂ L X⟩

end

end Limits

end CategoryTheory
