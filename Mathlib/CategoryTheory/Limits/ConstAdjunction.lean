/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Joël Riou
-/
import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Existence of (co)limits and adjoints of the constant functor

The main result in this file is `hasLimitsOfShape_iff_isLeftAdjoint_const` which
states that a category `C` has limits of shape `J` iff the constant
functor `C ⥤ J ⥤ C` has a right adjoint functor.

-/

namespace CategoryTheory

open Category

namespace Limits

variable (J C : Type*) [Category J] [Category C]

section

variable [HasLimitsOfShape J C]

/-- The constant functor and limit functor are adjoint to each other-/
noncomputable def constLimAdj : (Functor.const J : C ⥤ J ⥤ C) ⊣ lim where
  homEquiv c g :=
    { toFun := fun f => limit.lift _ ⟨c, f⟩
      invFun := fun f =>
        { app := fun j => f ≫ limit.π _ _ }
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  unit := { app := fun c => limit.lift _ ⟨_, 𝟙 _⟩ }
  counit := { app := fun g => { app := limit.π _ } }
  -- This used to be automatic before leanprover/lean4#2644
  homEquiv_unit := by
    -- Sad that aesop can no longer do this!
    intros
    dsimp
    ext
    simp
#align category_theory.limits.const_lim_adj CategoryTheory.Limits.constLimAdj

noncomputable instance : IsRightAdjoint (lim : (J ⥤ C) ⥤ C) :=
  ⟨_, constLimAdj J C⟩

noncomputable instance : IsLeftAdjoint (Functor.const J : C ⥤ J ⥤ C) :=
  ⟨_, constLimAdj J C⟩

instance limMap_mono' {F G : J ⥤ C} (α : F ⟶ G) [Mono α] : Mono (limMap α) :=
  (lim : (J ⥤ C) ⥤ C).map_mono α
#align category_theory.limits.lim_map_mono' CategoryTheory.Limits.limMap_mono'

end

section

variable [HasColimitsOfShape J C]

/-- The colimit functor and constant functor are adjoint to each other
-/
noncomputable def colimConstAdj : (colim : (J ⥤ C) ⥤ C) ⊣ Functor.const J where
  homEquiv f c :=
    { toFun := fun g =>
        { app := fun _ => colimit.ι _ _ ≫ g }
      invFun := fun g => colimit.desc _ ⟨_, g⟩
      left_inv := by aesop_cat
      right_inv := by aesop_cat }
  unit := { app := fun g => { app := colimit.ι _ } }
  counit := { app := fun c => colimit.desc _ ⟨_, 𝟙 _⟩ }
#align category_theory.limits.colim_const_adj CategoryTheory.Limits.colimConstAdj

noncomputable instance : IsLeftAdjoint (colim : (J ⥤ C) ⥤ C) :=
  ⟨_, colimConstAdj J C⟩

noncomputable instance : IsRightAdjoint (Functor.const J : C ⥤ J ⥤ C) :=
  ⟨_, colimConstAdj J C⟩

instance colimMap_epi' {F G : J ⥤ C} (α : F ⟶ G) [Epi α] :
    Epi (colimMap α) :=
  (colim : (J ⥤ C) ⥤ C).map_epi α
#align category_theory.limits.colim_map_epi' CategoryTheory.Limits.colimMap_epi'

end

section

variable {J C}
variable {F : (J ⥤ C) ⥤ C} (adj : Functor.const J ⊣ F) (X : J ⥤ C)

/-- A (limit) cone constructed from a right adjoint to the constant functor. -/
@[simps]
def coneOfConstAdjunction : Cone X where
  pt := F.obj X
  π := (adj.counit.app X)

/-- The cone `coneOfConstAdjunction adj X` is colimit. -/
def isLimitConeOfConstAdjunction : IsLimit (coneOfConstAdjunction adj X) where
  lift s := adj.homEquiv _ _ s.π
  fac s j := by
    have h₁ := NatTrans.congr_app (adj.counit.naturality s.π) j
    have h₂ := NatTrans.congr_app (adj.left_triangle_components (X := s.pt)) j
    dsimp at h₁ h₂ ⊢
    simp only [Adjunction.homEquiv_unit, assoc, h₁, reassoc_of% h₂]
  uniq s m hm := by
    dsimp
    symm
    rw [adj.homEquiv_apply_eq]
    ext j
    simp only [Adjunction.homEquiv_counit, NatTrans.comp_app,
      Functor.const_map_app, ← hm, coneOfConstAdjunction_π]

end

lemma hasLimitsOfShape_iff_isLeftAdjoint_const :
    HasLimitsOfShape J C ↔ Nonempty (IsLeftAdjoint (Functor.const J : C ⥤ J ⥤ C)) := by
  constructor
  · intro
    exact ⟨inferInstance⟩
  · intro ⟨_⟩
    constructor
    exact fun X => ⟨_, isLimitConeOfConstAdjunction (Adjunction.ofLeftAdjoint _) X⟩

section

variable {J C}
variable {G : (J ⥤ C) ⥤ C} (adj : G ⊣ Functor.const J) (X : J ⥤ C)

/-- A (colimit) cocone constructed from a left adjoint to the constant functor. -/
@[simps]
def coconeOfConstAdjunction : Cocone X where
  pt := G.obj X
  ι := (adj.unit.app X)

/-- The cocone `coconeOfConstAdjunction adj X` is limit. -/
def isColimitCoconeOfConstAdjunction : IsColimit (coconeOfConstAdjunction adj X) where
  desc s := (adj.homEquiv _ _).symm s.ι
  fac s j := by
    have h₁ := NatTrans.congr_app (adj.unit.naturality s.ι) j
    have h₂ := NatTrans.congr_app (adj.right_triangle_components (Y := s.pt)) j
    dsimp at h₁ h₂ ⊢
    simp only [Adjunction.homEquiv_counit, ← reassoc_of% h₁, h₂, comp_id]
  uniq s m hm := by
    dsimp
    rw [← adj.homEquiv_apply_eq]
    ext j
    simp only [Adjunction.homEquiv_unit, NatTrans.comp_app,
      Functor.const_map_app, ← hm, coconeOfConstAdjunction_ι]

end

lemma hasColimitsOfShape_iff_isRightAdjoint_const :
    HasColimitsOfShape J C ↔ Nonempty (IsRightAdjoint (Functor.const J : C ⥤ J ⥤ C)) := by
  constructor
  · intro
    exact ⟨inferInstance⟩
  · intro ⟨_⟩
    constructor
    exact fun X => ⟨_, isColimitCoconeOfConstAdjunction (Adjunction.ofRightAdjoint _) X⟩

end Limits

end CategoryTheory
