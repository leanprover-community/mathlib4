import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

namespace CategoryTheory

open Category Limits

variable {J C : Type _} [Category J] [Category C] [HasZeroMorphisms C]
  {F : J ⥤ ShortComplex C}

namespace ShortComplex

def isLimit_of_isLimitπ (c : Cone F)
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
    refine' Hom.mk (h₁.lift (π₁.mapCone s)) (h₂.lift (π₂.mapCone s))
      (h₃.lift (π₃.mapCone s)) (h₂.hom_ext (fun j => by
        dsimp
        rw [assoc, assoc, ← eq₁₂, reassoc_of% eq₁, eq₂, eq₁₂'])) (h₃.hom_ext (fun j => by
        dsimp
        rw [assoc, assoc, ← eq₂₃, reassoc_of% eq₂, eq₃, eq₂₃']))
  fac s j := by ext <;> apply IsLimit.fac
  uniq s m hm := by
    ext
    . exact h₁.uniq (π₁.mapCone s) _ (fun j => π₁.congr_map (hm j))
    . exact h₂.uniq (π₂.mapCone s) _ (fun j => π₂.congr_map (hm j))
    . exact h₃.uniq (π₃.mapCone s) _ (fun j => π₃.congr_map (hm j))

section

variable (F) [HasLimit (F ⋙ π₁)] [HasLimit (F ⋙ π₂)] [HasLimit (F ⋙ π₃)]

noncomputable def limitCone : Cone F :=
  Cone.mk (ShortComplex.mk (limMap (𝟙 F ◫ π₁Toπ₂)) (limMap (𝟙 F ◫ π₂Toπ₃)) (by aesop_cat))
    { app := fun j => Hom.mk (limit.π _ _) (limit.π _ _) (limit.π _ _)
        (by aesop_cat) (by aesop_cat)
      naturality := fun _ _ f => by
        ext
        all_goals
          dsimp
          erw [id_comp, limit.w] }

noncomputable def isLimitπ₁MapConeLimitCone : IsLimit (π₁.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))
noncomputable def isLimitπ₂MapConeLimitCone : IsLimit (π₂.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))
noncomputable def isLimitπ₃MapConeLimitCone : IsLimit (π₃.mapCone (limitCone F)) :=
  (IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext (Iso.refl _) (by aesop_cat)))

noncomputable def isLimitLimitCone : IsLimit (limitCone F) :=
  isLimit_of_isLimitπ _ (isLimitπ₁MapConeLimitCone F)
    (isLimitπ₂MapConeLimitCone F) (isLimitπ₃MapConeLimitCone F)

instance hasLimit_of_hasLimitπ : HasLimit F := ⟨⟨⟨_, isLimitLimitCone _⟩⟩⟩

noncomputable instance : PreservesLimit F π₁ :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (isLimitπ₁MapConeLimitCone F)
noncomputable instance : PreservesLimit F π₂ :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (isLimitπ₂MapConeLimitCone F)
noncomputable instance : PreservesLimit F π₃ :=
  preservesLimitOfPreservesLimitCone (isLimitLimitCone F) (isLimitπ₃MapConeLimitCone F)

end

instance hasLimitsOfShape [HasLimitsOfShape J C] :
  HasLimitsOfShape J (ShortComplex C) where

instance hasFiniteLimits [HasFiniteLimits C] :
  HasFiniteLimits (ShortComplex C) := ⟨fun _ _ _ => inferInstance⟩

noncomputable instance [HasLimitsOfShape J C] : PreservesLimitsOfShape J (π₁ : _ ⥤ C) where
noncomputable instance [HasLimitsOfShape J C] : PreservesLimitsOfShape J (π₂ : _ ⥤ C) where
noncomputable instance [HasLimitsOfShape J C] : PreservesLimitsOfShape J (π₃ : _ ⥤ C) where

noncomputable instance [HasFiniteLimits C] : PreservesFiniteLimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
noncomputable instance [HasFiniteLimits C] : PreservesFiniteLimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
noncomputable instance [HasFiniteLimits C] : PreservesFiniteLimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

instance preservesMonomorphisms_π₁ [HasLimitsOfShape WalkingCospan C] :
  Functor.PreservesMonomorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
instance preservesMonomorphisms_π₂ [HasLimitsOfShape WalkingCospan C] :
  Functor.PreservesMonomorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
instance preservesMonomorphisms_π₃ [HasLimitsOfShape WalkingCospan C] :
  Functor.PreservesMonomorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _

def isColimit_of_isColimitπ (c : Cocone F)
  (h₁ : IsColimit (π₁.mapCocone c)) (h₂ : IsColimit (π₂.mapCocone c))
  (h₃ : IsColimit (π₃.mapCocone c)) : IsColimit c where
  desc s := by
    have eq₁ := h₁.fac (π₁.mapCocone s)
    have eq₂ := h₂.fac (π₂.mapCocone s)
    have eq₃ := h₃.fac (π₃.mapCocone s)
    have eq₁₂ := fun j => (c.ι.app j).comm₁₂
    have eq₁₂' := fun j => (s.ι.app j).comm₁₂
    have eq₂₃ := fun j => (c.ι.app j).comm₂₃
    have eq₂₃' := fun j => (s.ι.app j).comm₂₃
    dsimp at eq₁ eq₂ eq₃ eq₁₂ eq₁₂' eq₂₃ eq₂₃'
    refine' Hom.mk (h₁.desc (π₁.mapCocone s)) (h₂.desc (π₂.mapCocone s))
      (h₃.desc (π₃.mapCocone s)) (h₁.hom_ext (fun j => by
        dsimp
        rw [reassoc_of% (eq₁ j), eq₁₂', reassoc_of% eq₁₂, eq₂])) (h₂.hom_ext (fun j => by
        dsimp
        rw [reassoc_of% (eq₂ j), eq₂₃', reassoc_of% eq₂₃, eq₃]))
  fac s j := by
    dsimp
    ext
    . apply IsColimit.fac h₁
    . apply IsColimit.fac h₂
    . apply IsColimit.fac h₃
  uniq s m hm := by
    ext
    . exact h₁.uniq (π₁.mapCocone s) _ (fun j => π₁.congr_map (hm j))
    . exact h₂.uniq (π₂.mapCocone s) _ (fun j => π₂.congr_map (hm j))
    . exact h₃.uniq (π₃.mapCocone s) _ (fun j => π₃.congr_map (hm j))
section

variable (F) [HasColimit (F ⋙ π₁)] [HasColimit (F ⋙ π₂)] [HasColimit (F ⋙ π₃)]

noncomputable def colimitCocone : Cocone F :=
  Cocone.mk (ShortComplex.mk (colimMap (𝟙 F ◫ π₁Toπ₂)) (colimMap (𝟙 F ◫ π₂Toπ₃)) (by aesop_cat))
    { app := fun j => Hom.mk (colimit.ι (F ⋙ π₁) _) (colimit.ι (F ⋙ π₂) _)
          (colimit.ι (F ⋙ π₃) _) (by aesop_cat) (by aesop_cat)
      naturality := fun _ _ f => by
        ext
        . dsimp
          erw [comp_id, colimit.w (F ⋙ π₁)]
        . dsimp
          erw [comp_id, colimit.w (F ⋙ π₂)]
        . dsimp
          erw [comp_id, colimit.w (F ⋙ π₃)] }

noncomputable def isColimitπ₁MapCoconeColimitCocone : IsColimit (π₁.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by aesop_cat)))
noncomputable def isColimitπ₂MapCoconeColimitCocone : IsColimit (π₂.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by aesop_cat)))
noncomputable def isColimitπ₃MapCoconeColimitCocone : IsColimit (π₃.mapCocone (colimitCocone F)) :=
  (IsColimit.ofIsoColimit (colimit.isColimit _) (Cocones.ext (Iso.refl _) (by aesop_cat)))

noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  isColimit_of_isColimitπ _ (isColimitπ₁MapCoconeColimitCocone F)
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

instance hasColimitsOfShape [HasColimitsOfShape J C] :
  HasColimitsOfShape J (ShortComplex C) where

instance hasFiniteColimits [HasFiniteColimits C] :
  HasFiniteColimits (ShortComplex C) := ⟨fun _ _ _ => inferInstance⟩

noncomputable instance [HasColimitsOfShape J C] : PreservesColimitsOfShape J (π₁ : _ ⥤ C) where
noncomputable instance [HasColimitsOfShape J C] : PreservesColimitsOfShape J (π₂ : _ ⥤ C) where
noncomputable instance [HasColimitsOfShape J C] : PreservesColimitsOfShape J (π₃ : _ ⥤ C) where

noncomputable instance [HasFiniteColimits C] : PreservesFiniteColimits (π₁ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
noncomputable instance [HasFiniteColimits C] : PreservesFiniteColimits (π₂ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩
noncomputable instance [HasFiniteColimits C] : PreservesFiniteColimits (π₃ : _ ⥤ C) :=
  ⟨fun _ _ _ => inferInstance⟩

instance preservesEpimorphismsπ₁ [HasColimitsOfShape WalkingSpan C] :
  Functor.PreservesEpimorphisms (π₁ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
instance preservesEpimorphismsπ₂ [HasColimitsOfShape WalkingSpan C] :
  Functor.PreservesEpimorphisms (π₂ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _
instance preservesEpimorphismsπ₃ [HasColimitsOfShape WalkingSpan C] :
  Functor.PreservesEpimorphisms (π₃ : _ ⥤ C) :=
  CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape _

end ShortComplex

end CategoryTheory
