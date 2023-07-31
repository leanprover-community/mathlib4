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

variable {J C : Type _} [Category J] [Category C] [HasZeroMorphisms C]
  {F : J ⥤ ShortComplex C}

namespace ShortComplex

/-- If a cone with values in `ShortComplex C` is such that it becomes limit
when we apply the three projections `ShortComplex C ⥤ C`, then it is limit. -/
def isLimitOfIsLimitπ (c : Cone F)
    (h₁ : IsLimit (π₁.mapCone c)) (h₂ : IsLimit (π₂.mapCone c))
    (h₃ : IsLimit (π₃.mapCone c)) : IsLimit c where
  lift s := by
    have eq₁ := h₁.fac (π₁.mapCone s)
    have eq₂ := h₂.fac (π₂.mapCone s)
    have eq₃ := h₃.fac (π₃.mapCone s)
    have eq₁₂ := fun j => (c.π.app j).comm₁₂
    have eq₁₂' := fun j => (s.π.app j).comm₁₂
    have eq₂₃ := fun j => (c.π.app j).comm₂₃
    have eq₂₃' := fun j => (s.π.app j).comm₂₃
    dsimp at eq₁ eq₂ eq₃ eq₁₂ eq₁₂' eq₂₃ eq₂₃'
    exact Hom.mk (h₁.lift (π₁.mapCone s)) (h₂.lift (π₂.mapCone s)) (h₃.lift (π₃.mapCone s))
      (h₂.hom_ext (fun j => by dsimp; rw [assoc, assoc, ← eq₁₂, reassoc_of% eq₁, eq₂, eq₁₂']))
      (h₃.hom_ext (fun j => by dsimp; rw [assoc, assoc, ← eq₂₃, reassoc_of% eq₂, eq₃, eq₂₃']))
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    . exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    . exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    . exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

section

variable (F) [HasLimit (F ⋙ π₁)] [HasLimit (F ⋙ π₂)] [HasLimit (F ⋙ π₃)]

/-- Construction of a limit cone for a functor `J ⥤ ShortComplex C` using the limits
of the three components `J ⥤ C`. -/
noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (whiskerLeft F π₁Toπ₂)) (limMap (whiskerLeft F π₂Toπ₃))
      (by aesop_cat))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by aesop_cat) (by aesop_cat)
      naturality := fun _ _ f => by
        ext
        all_goals
          dsimp
          erw [id_comp, limit.w] }

/-- `limitCone F` becomes limit after the application of `π₁ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))

/-- `limitCone F` becomes limit after the application of `π₂ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))

/-- `limitCone F` becomes limit after the application of `π₃ : ShortComplex C ⥤ C`. -/
noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))

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

end ShortComplex

end CategoryTheory
