/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Localization.StructuredArrow
import Mathlib.CategoryTheory.ClosedUnderIsomorphisms

/-!
# Pointwise right derived functors

-/

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type _} [Category C] [Category D] [Category D'] [Category H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  hasColimit' : HasPointwiseLeftKanExtensionAt W.Q F (W.Q.obj X)

abbrev HasPointwiseRightDerivedFunctor := ∀ (X : C), F.HasPointwiseRightDerivedFunctorAt W X

lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      HasPointwiseLeftKanExtensionAt L F (L.obj X) := by
  rw [← hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L F
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩

lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q F (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseRightDerivedFunctor W]

lemma hasPointwiseLeftKanExtension [L.IsLocalization W] :
      HasPointwiseLeftKanExtension L F := fun Y => by
    have := Localization.essSurj L W
    rw [← hasPointwiseLeftKanExtensionAt_iff_of_iso _ F (L.objObjPreimageIso Y),
      ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
    infer_instance

lemma hasRightDerivedFunctor_of_pointwise :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have := F.hasPointwiseLeftKanExtension W.Q W
    infer_instance

attribute [instance] hasRightDerivedFunctor_of_pointwise

variable {F L}

noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension := by
  have := hasPointwiseLeftKanExtension F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

end

section

variable {F L}

def isPointwiseLeftKanExtensionAtOfIso {G : D ⥤ H} (e : F ≅ L ⋙ G)
    [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s := by
    let S : Set (CostructuredArrow L (L.obj Y)) := fun j =>
      e.hom.app j.left ≫ G.map j.hom ≫ e.inv.app Y ≫
        NatTrans.app s.ι (CostructuredArrow.mk (𝟙 (L.obj Y))) = s.ι.app j
    /-suffices S = ⊤ by
      intro j
      have h : S j := by
        rw [this]
        tauto
      dsimp
      rw [assoc, h]-/
    intro j
    dsimp
    rw [assoc]
    refine Localization.induction_costructuredArrow L W S ?_ ?_ ?_ j
    · change _ = _
      simp
    · intro X₁ X₂ f φ hφ
      change _ = _ at hφ ⊢
      simp at hφ ⊢
      have eq := s.ι.naturality
        (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq
      rw [comp_id] at eq
      rw [← eq, ← hφ]
      simp
    · intro X₁ X₂ w hw φ hφ
      change _ = _ at hφ ⊢
      simp at hφ ⊢
      have eq := s.ι.naturality
        (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk
          ((Localization.isoOfHom L W w hw).inv ≫ φ))
      dsimp at eq
      rw [comp_id] at eq
      have : IsIso (F.map w) := by
        have := Localization.inverts L W w hw
        rw [← NatIso.naturality_2 e w]
        dsimp
        infer_instance
      rw [← cancel_epi (F.map w), eq, ← hφ]
      simp only [NatTrans.naturality_assoc, comp_obj, comp_map,
        NatIso.cancel_natIso_hom_left, ← G.map_comp_assoc,
        Localization.isoOfHom_hom_inv_id_assoc]
  uniq s m hm := by
    dsimp at m hm ⊢
    have eq := hm (CostructuredArrow.mk (𝟙 (L.obj Y)))
    dsimp at eq
    simp only [← eq, map_id, comp_id, Iso.inv_hom_id_app_assoc]

noncomputable def isPointwiseLeftKanExtensionOfIso {G : D ⥤ H} (e : F ≅ L ⋙ G)
    [L.IsLocalization W] :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtension := fun Y => by
  have := Localization.essSurj L W
  exact (LeftExtension.mk _ e.hom).isPointwiseLeftKanExtensionAtEquivOfIso' (L.objObjPreimageIso Y)
    (isPointwiseLeftKanExtensionAtOfIso W e _)

noncomputable def LeftExtension.isPointwiseLeftKanExtensionOfIsIso
    (E : LeftExtension L F) [IsIso E.hom]
    [L.IsLocalization W] :
    E.IsPointwiseLeftKanExtension :=
  Functor.isPointwiseLeftKanExtensionOfIso W (asIso E.hom)

lemma hasPointwiseRightDerivedFunctor_of_inverts
    (F : C ⥤ H) {W : MorphismProperty C} (hF : W.IsInvertedBy F) :
    F.HasPointwiseRightDerivedFunctor W := by
  intro X
  rw [hasPointwiseRightDerivedFunctorAt_iff F W.Q W]
  exact (isPointwiseLeftKanExtensionOfIso W
    (Localization.fac F hF W.Q).symm).hasPointwiseLeftKanExtension  _

end

end Functor

end CategoryTheory
