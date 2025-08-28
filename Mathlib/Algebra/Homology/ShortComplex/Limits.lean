/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Limits and colimits in the category of short complexes

In this file, it is shown if a category `C` with zero morphisms has limits
of a certain shape `J`, then it is also the case of the category `ShortComplex C`.

-/

namespace CategoryTheory

open Category Limits Functor

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
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₁₂ := fun j => (c.π.app j).comm₁₂
        have eq₁₂' := fun j => (s.π.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [assoc, assoc, ← eq₁₂, reassoc_of% eq₁, eq₂, eq₁₂'])
      comm₂₃ := h₃.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCone s)
        have eq₃ := h₃.fac (π₃.mapCone s)
        have eq₂₃ := fun j => (c.π.app j).comm₂₃
        have eq₂₃' := fun j => (s.π.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [assoc, assoc, ← eq₂₃, reassoc_of% eq₂, eq₃, eq₂₃']) }
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

section

variable (F)
variable [HasLimit (F ⋙ π₁)] [HasLimit (F ⋙ π₂)] [HasLimit (F ⋙ π₃)]

/-- Construction of a limit cone for a functor `J ⥤ ShortComplex C` using the limits
of the three components `J ⥤ C`. -/
noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by simp) (by simp)
      naturality := fun _ _ f => by
        ext <;> simp [← limit.w _ f] }

/-- `limitCone F` becomes limit after the application of `π₁ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by cat_disch)))

/-- `limitCone F` becomes limit after the application of `π₂ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by cat_disch)))

/-- `limitCone F` becomes limit after the application of `π₃ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by cat_disch)))

/-- `limitCone F` is limit. -/
noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  isLimitOfIsLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)

instance hasLimit_of_hasLimitπ : HasLimit F := ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩

noncomputable instance : PreservesLimit F π₁ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)

noncomputable instance : PreservesLimit F π₂ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)

noncomputable instance : PreservesLimit F π₃ :=
  preservesLimit_of_preserves_limit_cone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

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
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₁₂ := fun j => (c.ι.app j).comm₁₂
        have eq₁₂' := fun j => (s.ι.app j).comm₁₂
        dsimp at eq₁ eq₂ eq₁₂ eq₁₂' ⊢
        rw [reassoc_of% (eq₁ j), eq₁₂', reassoc_of% eq₁₂, eq₂])
      comm₂₃ := h₂.hom_ext (fun j => by
        have eq₂ := h₂.fac (π₂.mapCocone s)
        have eq₃ := h₃.fac (π₃.mapCocone s)
        have eq₂₃ := fun j => (c.ι.app j).comm₂₃
        have eq₂₃' := fun j => (s.ι.app j).comm₂₃
        dsimp at eq₂ eq₃ eq₂₃ eq₂₃' ⊢
        rw [reassoc_of% (eq₂ j), eq₂₃', reassoc_of% eq₂₃, eq₃]) }
  fac s j := by
    ext
    · apply IsColimit.fac h₁
    · apply IsColimit.fac h₂
    · apply IsColimit.fac h₃
  uniq s m hm := by
    ext
    · exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
    · exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
    · exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))

section

variable (F)
variable [HasColimit (F ⋙ π₁)] [HasColimit (F ⋙ π₂)] [HasColimit (F ⋙ π₃)]

/-- Construction of a colimit cocone for a functor `J ⥤ ShortComplex C` using the colimits
of the three components `J ⥤ C`. -/
noncomputable def colimitCocone : Cocone F :=
  Cocone.mk (ShortComplex.mk (colimMap (whiskerLeft F π₁Toπ₂)) (colimMap (whiskerLeft F π₂Toπ₃))
      (by cat_disch))
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
        (colimit.ι (F ⋙ π₃) _) (by simp) (by simp)
      naturality := fun _ _ f => by
        ext
        · simp [← colimit.w (F ⋙ π₁) f]
        · simp [← colimit.w (F ⋙ π₂) f]
        · simp [← colimit.w (F ⋙ π₃) f] }

/-- `colimitCocone F` becomes colimit after the application of `π₁ : ShortComplex C ⥤ C`. -/
noncomputable def isColimitπ₁MapCoconeColimitCocone :
    IsColimit (π₁.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by cat_disch)))

/-- `colimitCocone F` becomes colimit after the application of `π₂ : ShortComplex C ⥤ C`. -/
noncomputable def isColimitπ₂MapCoconeColimitCocone :
    IsColimit (π₂.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by cat_disch)))

/-- `colimitCocone F` becomes colimit after the application of `π₃ : ShortComplex C ⥤ C`. -/
noncomputable def isColimitπ₃MapCoconeColimitCocone :
    IsColimit (π₃.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by cat_disch)))

/-- `colimitCocone F` is colimit. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimitOfIsColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F) (isColimitπ₃MapCoconeColimitCocone F)

instance hasColimit_of_hasColimitπ : HasColimit F := ⟨⟨⟨_, isColimitColimitCocone _⟩⟩⟩

noncomputable instance : PreservesColimit F π₁ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₁MapCoconeColimitCocone F)

noncomputable instance : PreservesColimit F π₂ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (isColimitπ₂MapCoconeColimitCocone F)

noncomputable instance : PreservesColimit F π₃ :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
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
