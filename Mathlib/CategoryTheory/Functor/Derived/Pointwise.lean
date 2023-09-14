import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.RespectsIso

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C D D' H : Type _} [Category C] [Category D] [Category D'] [Category H]
  (F' : D ⥤ H) (F : C ⥤ H) (L : C ⥤ D) (α : F ⟶ L ⋙ F') (W : MorphismProperty C)

class HasPointwiseRightDerivedFunctorAt (X : C) : Prop where
  hasColimit' : F.HasPointwiseLeftKanExtensionAt W.Q (W.Q.obj X)

abbrev HasPointwiseRightDerivedFunctor := ∀ (X : C), F.HasPointwiseRightDerivedFunctorAt W X

lemma hasPointwiseRightDerivedFunctorAt_iff [L.IsLocalization W] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseLeftKanExtensionAt L (L.obj X) := by
  rw [← F.hasPointwiseLeftKanExtensionAt_iff_of_equivalence W.Q L
    (Localization.uniq W.Q L W) (Localization.compUniqFunctor W.Q L W) (W.Q.obj X) (L.obj X)
    ((Localization.compUniqFunctor W.Q L W).app X)]
  exact ⟨fun h => h.hasColimit', fun h => ⟨h⟩⟩

lemma hasPointwiseRightDerivedFunctorAt_iff_of_mem {X Y : C} (w : X ⟶ Y) (hw : W w) :
    F.HasPointwiseRightDerivedFunctorAt W X ↔
      F.HasPointwiseRightDerivedFunctorAt W Y := by
  simp only [F.hasPointwiseRightDerivedFunctorAt_iff W.Q W]
  exact F.hasPointwiseLeftKanExtensionAt_iff_of_iso W.Q (Localization.isoOfHom W.Q W w hw)

section

variable [F.HasPointwiseRightDerivedFunctor W]

lemma hasPointwiseLeftKanExtension [L.IsLocalization W] :
      F.HasPointwiseLeftKanExtension L := fun Y => by
    have := Localization.essSurj L W
    rw [← F.hasPointwiseLeftKanExtensionAt_iff_of_iso _ (L.objObjPreimageIso Y),
      ← F.hasPointwiseRightDerivedFunctorAt_iff L W]
    infer_instance

lemma hasRightDerivedFunctor_of_pointwise :
    F.HasRightDerivedFunctor W where
  hasLeftKanExtension' := by
    have pif := F.hasPointwiseLeftKanExtension W.Q W
    infer_instance

variable {F L}

noncomputable def isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
     [L.IsLocalization W] [F'.IsRightDerivedFunctor α W] :
    (LeftExtension.mk _ α).IsPointwiseLeftKanExtension := by
  have := hasPointwiseLeftKanExtension F L
  have := IsRightDerivedFunctor.isLeftKanExtension F' α W
  exact isPointwiseLeftKanExtensionOfIsLeftKanExtension F' α

end

/-section

variable {Y : C} (S : Set (CostructuredArrow L (L.obj Y)))
  [L.IsLocalization W]
  (hS₀ : CostructuredArrow.mk (𝟙 (L.obj Y)) ∈ S)
  (hS₁ : ∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂) (φ : L.obj X₂ ⟶ L.obj Y),
    CostructuredArrow.mk φ ∈ S → CostructuredArrow.mk (L.map f ≫ φ) ∈ S)
  (hS₂ : ∀ ⦃X₁ X₂ : C⦄ (w : X₁ ⟶ X₂) (hw : W w) (φ : L.obj X₁ ⟶ L.obj Y),
    CostructuredArrow.mk φ ∈ S → CostructuredArrow.mk ((Localization.isoOfHom L W w hw).inv  ≫ φ) ∈ S)

lemma Localization.induction_costructuredArrow [L.IsLocalization W] : S = ⊤ := by
  have := hS₀
  have := hS₁
  have := hS₂
  sorry

end

section

variable {F L}

def isPointwiseLeftKanExtensionAtOfInverts {G : D ⥤ H} (e : F ≅ L ⋙ G)
    [L.IsLocalization W] (Y : C) :
    (LeftExtension.mk _ e.hom).IsPointwiseLeftKanExtensionAt (L.obj Y) where
  desc s := e.inv.app Y ≫ s.ι.app (CostructuredArrow.mk (𝟙 (L.obj Y)))
  fac s := by
    let S : Set (CostructuredArrow L (L.obj Y)) := fun j =>
      e.hom.app j.left ≫ G.map j.hom ≫ e.inv.app Y ≫
        NatTrans.app s.ι (CostructuredArrow.mk (𝟙 (L.obj Y))) = s.ι.app j
    suffices S = ⊤ by
      intro j
      have h : S j := by
        rw [this]
        tauto
      dsimp
      rw [assoc, h]
    apply Localization.induction_costructuredArrow L W
    · change _ = _
      simp
    · intro X₁ X₂ f φ hφ
      change _ = _ at hφ ⊢
      simp at hφ ⊢
      have eq := s.ι.naturality (CostructuredArrow.homMk f : CostructuredArrow.mk (L.map f ≫ φ) ⟶ CostructuredArrow.mk φ)
      dsimp at eq
      rw [comp_id] at eq
      rw [← eq, ← hφ]
      simp
    · intro X₁ X₂ w hw φ hφ
      change _ = _ at hφ ⊢
      simp at hφ ⊢
      have eq := s.ι.naturality (CostructuredArrow.homMk w : CostructuredArrow.mk φ ⟶ CostructuredArrow.mk ((Localization.isoOfHom L W w hw).inv ≫ φ))
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

end-/

end Functor

end CategoryTheory
