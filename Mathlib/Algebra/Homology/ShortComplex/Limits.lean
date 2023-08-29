/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limits and colimits in the category of short complexes

In this file, it is shown if a category `C` with zero morphisms has limits
of a certain shape `J`, then it is also the case of the category `ShortComplex C`.

TODO (@rioujoel): Do the same for colimits.

-/

namespace CategoryTheory

open Category Limits

variable {J C : Type*} [Category J] [Category C] [HasZeroMorphisms C]
  {F : J ⥤ ShortComplex C}

namespace ShortComplex

/-- If a cone with values in `ShortComplex C` is such that it becomes limit
when we apply the three projections `ShortComplex C ⥤ C`, then it is limit. -/
def isLimitOfIsLimitπ (c : Cone F)
    (h₁ : IsLimit (π₁.mapCone c)) (h₂ : IsLimit (π₂.mapCone c))
    (h₃ : IsLimit (π₃.mapCone c)) : IsLimit c where
  lift s :=
    { τ₁ := h₁.lift (π₁.mapCone s)
      τ₂ := h₂.lift (π₂.mapCone s)
      τ₃ := h₃.lift (π₃.mapCone s)
      comm₁₂ := h₂.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCone s)
        -- ⊢ (IsLimit.lift h₁ (π₁.mapCone s) ≫ c.pt.f) ≫ NatTrans.app (π₂.mapCone c).π j  …
        have eq₂ := h₂.fac (π₂.mapCone s)
        -- ⊢ (IsLimit.lift h₁ (π₁.mapCone s) ≫ c.pt.f) ≫ NatTrans.app (π₂.mapCone c).π j  …
        have eq₁₂ := fun j => (c.π.app j).comm₁₂
        -- ⊢ (IsLimit.lift h₁ (π₁.mapCone s) ≫ c.pt.f) ≫ NatTrans.app (π₂.mapCone c).π j  …
        have eq₁₂' := fun j => (s.π.app j).comm₁₂
        -- ⊢ (IsLimit.lift h₁ (π₁.mapCone s) ≫ c.pt.f) ≫ NatTrans.app (π₂.mapCone c).π j  …
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        -- ⊢ (IsLimit.lift h₁ (π₁.mapCone s) ≫ c.pt.f) ≫ (NatTrans.app c.π j).τ₂ = (s.pt. …
        rw [assoc, assoc, ← eq₁₂, reassoc_of% eq₁, eq₂, eq₁₂'])
        -- 🎉 no goals
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        -- ⊢ (IsLimit.lift h₂ (π₂.mapCone s) ≫ c.pt.g) ≫ NatTrans.app (π₃.mapCone c).π j  …
        have eq₃ := h₃.fac (π₃.mapCone s)
        -- ⊢ (IsLimit.lift h₂ (π₂.mapCone s) ≫ c.pt.g) ≫ NatTrans.app (π₃.mapCone c).π j  …
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        -- ⊢ (IsLimit.lift h₂ (π₂.mapCone s) ≫ c.pt.g) ≫ NatTrans.app (π₃.mapCone c).π j  …
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        -- ⊢ (IsLimit.lift h₂ (π₂.mapCone s) ≫ c.pt.g) ≫ NatTrans.app (π₃.mapCone c).π j  …
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        -- ⊢ (IsLimit.lift h₂ (π₂.mapCone s) ≫ c.pt.g) ≫ (NatTrans.app c.π j).τ₃ = (s.pt. …
        rw [assoc, assoc, ← eq₂₃, reassoc_of% eq₂, eq₃, eq₂₃']) }
        -- 🎉 no goals
  fac s j := by ext <;> apply IsLimit.fac
                        -- 🎉 no goals
                        -- 🎉 no goals
                        -- 🎉 no goals
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
      -- 🎉 no goals
    · exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
      -- 🎉 no goals
    · exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))
      -- 🎉 no goals

section

variable (F) [HasLimit (F ⋙ π₁)] [HasLimit (F ⋙ π₂)] [HasLimit (F ⋙ π₃)]

/-- Construction of a limit cone for a functor `J ⥤ ShortComplex C` using the limits
of the three components `J ⥤ C`. -/
noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by aesop_cat))
          -- 🎉 no goals
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by aesop_cat) (by aesop_cat)
            -- 🎉 no goals
                           -- 🎉 no goals
      naturality := fun _ _ f => by
        ext
        all_goals
          dsimp
          erw [id_comp, limit.w] }

/-- `limitCone F` becomes limit after the application of `π₁ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))
                                                                    -- 🎉 no goals

/-- `limitCone F` becomes limit after the application of `π₂ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))
                                                                    -- 🎉 no goals

/-- `limitCone F` becomes limit after the application of `π₃ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))
                                                                    -- 🎉 no goals

/-- `limitCone F` is limit. -/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)

instance hasLimit_of_hasLimitπ : HasLimit F := ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩

noncomputable instance : PreservesLimit F π₁ :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)

noncomputable instance : PreservesLimit F π₂ :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)

noncomputable instance : PreservesLimit F π₃ :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

end

section

variable [HasLimitsOfShape J C]

instance hasLimitsOfShape :
    HasLimitsOfShape J (ShortComplex C) where

noncomputable instance : PreservesLimitsOfShape J (π₁ : _ ⥤ C) where

noncomputable instance : PreservesLimitsOfShape J (π₂ : _ ⥤ C) where

noncomputable instance : PreservesLimitsOfShape J (π₃ : _ ⥤ C) where

end

section

variable [HasFiniteLimits C]

instance hasFiniteLimits : HasFiniteLimits (ShortComplex C) :=
  ⟨fun _ _ _ => inferInstance⟩

noncomputable instance : PreservesFiniteLimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

noncomputable instance : PreservesFiniteLimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

noncomputable instance : PreservesFiniteLimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

end

section

variable [HasLimitsOfShape WalkingCospan C]

instance preservesMonomorphisms_π₁ :
    Functor.PreservesMonomorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

instance preservesMonomorphisms_π₂ :
    Functor.PreservesMonomorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

instance preservesMonomorphisms_π₃ :
    Functor.PreservesMonomorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

end

/-- If a cocone with values in `ShortComplex C` is such that it becomes colimit
when we apply the three projections `ShortComplex C ⥤ C`, then it is colimit. -/
def isColimitOfIsColimitπ (c : Cocone F)
    (h₁ : IsColimit (π₁.mapCocone c)) (h₂ : IsColimit (π₂.mapCocone c))
    (h₃ : IsColimit (π₃.mapCocone c)) : IsColimit c where
  desc s :=
    { τ₁ := h₁.desc (π₁.mapCocone s)
      τ₂ := h₂.desc (π₂.mapCocone s)
      τ₃ := h₃.desc (π₃.mapCocone s)
      comm₁₂ := h₁.hom_ext (fun j => by
        have eq₁ := h₁.fac (π₁.mapCocone s)
        -- ⊢ NatTrans.app (π₁.mapCocone c).ι j ≫ IsColimit.desc h₁ (π₁.mapCocone s) ≫ s.p …
        have eq₂ := h₂.fac (π₂.mapCocone s)
        -- ⊢ NatTrans.app (π₁.mapCocone c).ι j ≫ IsColimit.desc h₁ (π₁.mapCocone s) ≫ s.p …
        have eq₁₂ := fun j => (c.ι.app j).comm₁₂
        -- ⊢ NatTrans.app (π₁.mapCocone c).ι j ≫ IsColimit.desc h₁ (π₁.mapCocone s) ≫ s.p …
        have eq₁₂' := fun j => (s.ι.app j).comm₁₂
        -- ⊢ NatTrans.app (π₁.mapCocone c).ι j ≫ IsColimit.desc h₁ (π₁.mapCocone s) ≫ s.p …
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        -- ⊢ (NatTrans.app c.ι j).τ₁ ≫ IsColimit.desc h₁ (π₁.mapCocone s) ≫ s.pt.f = (Nat …
        rw [reassoc_of% (eq₁ j), eq₁₂', reassoc_of% eq₁₂, eq₂])
        -- 🎉 no goals
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        -- ⊢ NatTrans.app (π₂.mapCocone c).ι j ≫ IsColimit.desc h₂ (π₂.mapCocone s) ≫ s.p …
        have eq₃ := h₃.fac (π₃.mapCocone s)
        -- ⊢ NatTrans.app (π₂.mapCocone c).ι j ≫ IsColimit.desc h₂ (π₂.mapCocone s) ≫ s.p …
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        -- ⊢ NatTrans.app (π₂.mapCocone c).ι j ≫ IsColimit.desc h₂ (π₂.mapCocone s) ≫ s.p …
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        -- ⊢ NatTrans.app (π₂.mapCocone c).ι j ≫ IsColimit.desc h₂ (π₂.mapCocone s) ≫ s.p …
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        -- ⊢ (NatTrans.app c.ι j).τ₂ ≫ IsColimit.desc h₂ (π₂.mapCocone s) ≫ s.pt.g = (Nat …
        rw [reassoc_of% (eq₂ j), eq₂₃', reassoc_of% eq₂₃, eq₃]) }
        -- 🎉 no goals
  fac s j := by
    ext
    · apply IsColimit.fac h₁
      -- 🎉 no goals
    · apply IsColimit.fac h₂
      -- 🎉 no goals
    · apply IsColimit.fac h₃
      -- 🎉 no goals
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
      -- 🎉 no goals
    · exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
      -- 🎉 no goals
    · exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))
      -- 🎉 no goals

section

variable (F) [HasColimit (F ⋙ π₁)] [HasColimit (F ⋙ π₂)] [HasColimit (F ⋙ π₃)]

/-- Construction of a colimit cocone for a functor `J ⥤ ShortComplex C` using the colimits
of the three components `J ⥤ C`. -/
noncomputable def colimitCocone : Cocone F :=
  Cocone.mk (ShortComplex.mk (colimMap (whiskerLeft F π₁Toπ₂)) (colimMap (whiskerLeft F π₂Toπ₃))
      (by aesop_cat))
          -- 🎉 no goals
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
        (colimit.ι (F ⋙ π₃) _) (by aesop_cat) (by aesop_cat)
                                   -- 🎉 no goals
                                                  -- 🎉 no goals
      naturality := fun _ _ f => by
        ext
        · dsimp; erw [comp_id, colimit.w (F ⋙ π₁)]
          -- ⊢ (F.map f).τ₁ ≫ colimit.ι (F ⋙ π₁) x✝ = colimit.ι (F ⋙ π₁) x✝¹ ≫ 𝟙 (colimit ( …
                 -- 🎉 no goals
        · dsimp; erw [comp_id, colimit.w (F ⋙ π₂)]
          -- ⊢ (F.map f).τ₂ ≫ colimit.ι (F ⋙ π₂) x✝ = colimit.ι (F ⋙ π₂) x✝¹ ≫ 𝟙 (colimit ( …
                 -- 🎉 no goals
        · dsimp; erw [comp_id, colimit.w (F ⋙ π₃)] }
          -- ⊢ (F.map f).τ₃ ≫ colimit.ι (F ⋙ π₃) x✝ = colimit.ι (F ⋙ π₃) x✝¹ ≫ 𝟙 (colimit ( …
                 -- 🎉 no goals

/-- `colimitCocone F` becomes colimit after the application of `π₁ : ShortComplex C ⥤ C`. -/
noncomputable def isColimitπ₁MapCoconeColimitCocone :
    IsColimit (π₁.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by aesop_cat)))
                                                                              -- 🎉 no goals

/-- `colimitCocone F` becomes colimit after the application of `π₂ : ShortComplex C ⥤ C`. -/
noncomputable def isColimitπ₂MapCoconeColimitCocone :
    IsColimit (π₂.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by aesop_cat)))
                                                                              -- 🎉 no goals

/-- `colimitCocone F` becomes colimit after the application of `π₃ : ShortComplex C ⥤ C`. -/
noncomputable def isColimitπ₃MapCoconeColimitCocone :
    IsColimit (π₃.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by aesop_cat)))
                                                                              -- 🎉 no goals

/-- `colimitCocone F` is colimit. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)

instance hasColimit_of_hasColimitπ : HasColimit F := ⟨⟨⟨_, isColimitColimitCocone _⟩⟩⟩

noncomputable instance : PreservesColimit F π₁ :=
  preservesColimitOfPreservesColimitCocone (isColimitColimitCocone F)
    (isColimitπ₁MapCoconeColimitCocone F)

noncomputable instance : PreservesColimit F π₂ :=
  preservesColimitOfPreservesColimitCocone (isColimitColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F)

noncomputable instance : PreservesColimit F π₃ :=
  preservesColimitOfPreservesColimitCocone (isColimitColimitCocone F)
    (isColimitπ₃MapCoconeColimitCocone F)

end

section

variable [HasColimitsOfShape J C]

instance hasColimitsOfShape :
    HasColimitsOfShape J (ShortComplex C) where

noncomputable instance : PreservesColimitsOfShape J (π₁ : _ ⥤ C) where

noncomputable instance : PreservesColimitsOfShape J (π₂ : _ ⥤ C) where

noncomputable instance : PreservesColimitsOfShape J (π₃ : _ ⥤ C) where

end

section

variable [HasFiniteColimits C]

instance hasFiniteColimits : HasFiniteColimits (ShortComplex C) :=
  ⟨fun _ _ _ => inferInstance⟩

noncomputable instance : PreservesFiniteColimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

noncomputable instance : PreservesFiniteColimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

noncomputable instance : PreservesFiniteColimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

end

section

variable [HasColimitsOfShape WalkingSpan C]

instance preservesEpimorphisms_π₁ :
    Functor.PreservesEpimorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

instance preservesEpimorphisms_π₂ :
    Functor.PreservesEpimorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

instance preservesEpimorphisms_π₃ :
    Functor.PreservesEpimorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

end

end ShortComplex

end CategoryTheory
