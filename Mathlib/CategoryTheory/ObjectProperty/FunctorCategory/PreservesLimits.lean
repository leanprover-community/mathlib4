/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.ColimitLimit
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
a property of objects in the functor category `J ⥤ C`, and show that
it is stable under colimits of shape `K'` when they
commute to limits of shape `K` (resp. to finite limits).

-/

public section

namespace CategoryTheory

open Limits

variable {J C : Type*} (K K' : Type*)
  [Category* K] [Category* K'] [Category* J] [Category* C]

namespace ObjectProperty

variable {K} in
/-- The property of objects in the functor category `J ⥤ C`
which preserves the limit of a functor `F : K ⥤ J`. -/
abbrev preservesLimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesLimit F

@[simp]
lemma preservesLimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesLimit F G ↔ PreservesLimit F G := Iff.rfl

lemma congr_preservesLimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesLimit (C := C) F = preservesLimit (C := C) F' := by
  ext G
  simp_rw [preservesLimit_iff]
  exact ⟨fun h ↦ preservesLimit_of_iso_diagram _ e,
    fun h ↦ preservesLimit_of_iso_diagram _ e.symm⟩

instance (F : K ⥤ J) : (preservesLimit (C := C) F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesLimit_of_natIso _ e

variable {K} in
/-- The property of objects in the functor category `J ⥤ C`
which preserves the colimit of a functor `F : K ⥤ J`. -/
abbrev preservesColimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesColimit F

@[simp]
lemma preservesColimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesColimit F G ↔ PreservesColimit F G := Iff.rfl

lemma congr_preservesColimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesColimit (C := C) F = preservesColimit (C := C) F' := by
  ext G
  simp_rw [preservesColimit_iff]
  exact ⟨fun h ↦ preservesColimit_of_iso_diagram _ e,
    fun h ↦ preservesColimit_of_iso_diagram _ e.symm⟩

instance (F : K ⥤ J) : (preservesColimit (C := C) F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesColimit_of_natIso _ e

/-- The property of objects in the functor category `J ⥤ C`
which preserves limits of shape `K`. -/
abbrev preservesLimitsOfShape : ObjectProperty (J ⥤ C) := PreservesLimitsOfShape K

@[simp]
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl

lemma preservesLimitsOfShape_eq_iSup :
    preservesLimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesLimit F := by
  ext G
  simp only [preservesLimitsOfShape_iff, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

variable (J C) {K K'} in
lemma congr_preservesLimitsOfShape (e : K ≌ K') :
    preservesLimitsOfShape (J := J) (C := C) K = preservesLimitsOfShape K' := by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesLimitsOfShape_of_equiv e _,
    fun _ ↦ preservesLimitsOfShape_of_equiv e.symm _⟩

instance : (preservesLimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms := by
  rw [preservesLimitsOfShape_eq_iSup]
  infer_instance

/-- The property of objects in the functor category `J ⥤ C`
which preserves colimits of shape `K`. -/
abbrev preservesColimitsOfShape : ObjectProperty (J ⥤ C) := PreservesColimitsOfShape K

@[simp]
lemma preservesColimitsOfShape_iff (F : J ⥤ C) :
    preservesColimitsOfShape K F ↔ PreservesColimitsOfShape K F := Iff.rfl

lemma preservesColimitsOfShape_eq_iSup :
    preservesColimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesColimit F := by
  ext G
  simp only [preservesColimitsOfShape_iff, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

variable (J C) {K K'} in
lemma congr_preservesColimitsOfShape (e : K ≌ K') :
    preservesColimitsOfShape (J := J) (C := C) K = preservesColimitsOfShape K' := by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesColimitsOfShape_of_equiv e _,
    fun _ ↦ preservesColimitsOfShape_of_equiv e.symm _⟩

instance : (preservesColimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms := by
  rw [preservesColimitsOfShape_eq_iSup]
  infer_instance

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite limits. -/
abbrev preservesFiniteLimits : ObjectProperty (J ⥤ C) := PreservesFiniteLimits

@[simp]
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl

instance : (preservesFiniteLimits (J := J) (C := C)).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesFiniteLimits_of_natIso e

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite colimits. -/
abbrev preservesFiniteColimits : ObjectProperty (J ⥤ C) := PreservesFiniteColimits

instance : (preservesFiniteColimits (J := J) (C := C)).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesFiniteColimits_of_natIso e

@[simp]
lemma preservesFiniteColimits_iff (F : J ⥤ C) :
    preservesFiniteColimits F ↔ PreservesFiniteColimits F := Iff.rfl

instance [HasColimitsOfShape K' C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderColimitsOfShape K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsLimits _
        (fun k' ↦ isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents
        (fun j ↦ (colimit.isColimit (h.diag.flip.obj j)).coconePointUniqueUpToIso
          (isColimitOfPreserves ((evaluation _ _).obj j) h.isColimit))
    exact preservesLimitsOfShape_of_natIso e

instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ ↦ (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

instance [HasColimitsOfShape K' C] [HasLimitsOfShape K C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (preservesColimitsOfShape K' : ObjectProperty (J ⥤ C)) K where
  limitsOfShape_le := by
    have : PreservesColimitsOfShape K' (lim (J := K) (C := C)) := by
      rwa [preservesColimitsOfShape_lim_iff_preservesLimitsOfShape_colim]
    intro G ⟨p⟩
    have := p.prop_diag_obj
    have : PreservesColimitsOfShape K' p.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsColimits _
        (fun k ↦ isColimitOfPreserves (p.diag.obj k) hc)⟩⟩⟩
    let e : G ≅ p.diag.flip ⋙ lim :=
      NatIso.ofComponents
        (fun j ↦ (isLimitOfPreserves ((evaluation _ _).obj j) p.isLimit).conePointUniqueUpToIso
          (limit.isLimit (p.diag.flip.obj j))) (fun {j₁ j₂} f ↦ by
            dsimp
            ext
            simp [IsLimit.conePointUniqueUpToIso])
    exact preservesColimitsOfShape_of_natIso e.symm

instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] [HasFiniteLimits C] :
    ObjectProperty.IsClosedUnderFiniteLimits
      (preservesColimitsOfShape K' : ObjectProperty (J ⥤ C)) where

instance (F : K ⥤ J) [HasColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesColimit F : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    intro G ⟨p⟩
    refine ⟨fun {c} hc ↦ ⟨?_⟩⟩
    let hp (j : J):= isColimitOfPreserves ((evaluation _ _).obj j) p.isColimit
    have := p.prop_diag_obj
    let s' (s : Cocone (F ⋙ G)) (k' : K') : Cocone (F ⋙ p.diag.obj k') :=
      { pt := s.pt
        ι.app k := (p.ι.app k').app _ ≫ s.ι.app k
        ι.naturality _ _ f := by simp [dsimp% s.w f] }
    let s'' (s : Cocone (F ⋙ G)) : Cocone (p.diag ⋙ (evaluation J C).obj c.pt) :=
      { pt := s.pt
        ι.app k' := (isColimitOfPreserves (p.diag.obj k') hc).desc (s' s k')
        ι.naturality {k₁' k₂'} f :=
          (isColimitOfPreserves (p.diag.obj k₁') hc).hom_ext (fun k ↦ by
            simp [s', dsimp% (isColimitOfPreserves (p.diag.obj k₁') hc).fac (s' s k₁') k,
              dsimp% (isColimitOfPreserves (p.diag.obj k₂') hc).fac (s' s k₂') k]) }
    have hs'' (s : Cocone (F ⋙ G)) (k : K) (k' : K'):
        (p.diag.obj k').map (c.ι.app k) ≫ (s'' s).ι.app k' =
        (p.ι.app k').app (F.obj k) ≫ s.ι.app k :=
      (isColimitOfPreserves (p.diag.obj k') hc).fac (s' s k') k
    exact {
      desc s := (hp c.pt).desc (s'' s)
      fac s k :=
        (hp (F.obj k)).hom_ext (fun k' ↦ by
          simp [← NatTrans.naturality_assoc, dsimp% (hp c.pt).fac (s'' s) k', hs''])
      uniq s m hm :=
        (hp c.pt).hom_ext
          (fun k' ↦ (isColimitOfPreserves (p.diag.obj k') hc).hom_ext
            (by simp [dsimp% hm, dsimp% (hp c.pt).fac (s'' s) k', hs''])) }

instance [HasColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesColimitsOfShape K : ObjectProperty (J ⥤ C)) K' := by
  rw [preservesColimitsOfShape_eq_iSup]
  infer_instance

instance [HasFiniteColimits C] :
    ObjectProperty.IsClosedUnderFiniteColimits
      (preservesColimitsOfShape K : ObjectProperty (J ⥤ C)) where

end ObjectProperty

end CategoryTheory
