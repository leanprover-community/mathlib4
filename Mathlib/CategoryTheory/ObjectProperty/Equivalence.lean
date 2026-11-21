/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice

/-!
# Equivalence of full subcategories

The inclusion functor `P.FullSubcategory ⥤ Q.FullSubcategory` induced
by an inequality `P ≤ Q` in `ObjectProperty C` is an equivalence iff
`Q ≤ P.isoClosure`.
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]

lemma Functor.isEquivalence_iff_essImage_of_full_of_faithful
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    [F.Full] [F.Faithful] :
    F.IsEquivalence ↔ F.essImage = ⊤ := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · rw [← F.essSurj_iff_essImage_eq_top]
    infer_instance
  · exact { essSurj := by rwa [F.essSurj_iff_essImage_eq_top] }

namespace ObjectProperty

variable {P Q : ObjectProperty C} (h : P ≤ Q)

lemma essSurj_ιOfLE_iff : (ιOfLE h).EssSurj ↔ Q ≤ P.isoClosure := by
  refine ⟨fun _ X hX ↦ ?_, fun hPQ ↦ ⟨fun ⟨Y, hY⟩ ↦ ?_⟩⟩
  · exact ⟨_, ((ιOfLE h).objPreimage ⟨X, hX⟩).property,
      ⟨Q.ι.mapIso ((ιOfLE h).objObjPreimageIso ⟨X, hX⟩).symm⟩⟩
  · obtain ⟨X, hX, ⟨e⟩⟩ := hPQ _ hY
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso e.symm⟩⟩

lemma isEquivalence_ιOfLE_iff : (ιOfLE h).IsEquivalence ↔ Q ≤ P.isoClosure := by
  rw [← essSurj_ιOfLE_iff h]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ { }⟩

instance : (ιOfLE P.le_isoClosure).IsEquivalence := by rw [isEquivalence_ιOfLE_iff]

variable (C) in
/-- The equivalence between the full subcategory `⊤` of a category `C` and `C` itself. -/
@[simps]
def topEquivalence : ObjectProperty.FullSubcategory (C := C) ⊤ ≌ C where
  functor := ObjectProperty.ι _
  inverse := ObjectProperty.lift _ (𝟭 _) (by simp)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

lemma isEquivalence_ι (h : P = ⊤) : P.ι.IsEquivalence := by
  rw [h]
  exact (topEquivalence C).isEquivalence_functor

lemma isEquivalence_lift_iff {D : Type*} [Category* D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) [F.Full] [F.Faithful] (hF : ∀ (X : C), P (F.obj X)) :
    (P.lift F hF).IsEquivalence ↔ F.essImage = P.isoClosure := by
  suffices H : F.essImage.inverseImage P.ι = ⊤ ↔ (F.essImage = P.isoClosure) by
    rwa [Functor.isEquivalence_iff_essImage_of_full_of_faithful, essImage_lift]
  simp only [← map_eq_map_iff_of_isClosedUnderIsomorphisms P.ι,
    map_inverseImage, ObjectProperty.map_top,
    essImage_ι, le_antisymm_iff, inf_le_right, le_inf_iff,
    le_refl, and_true, true_and, iff_and_self]
  rintro hx X ⟨Y, ⟨e⟩⟩
  exact prop_isoClosure (hF Y) e.hom

end ObjectProperty

namespace Equivalence

variable {P : ObjectProperty C} {Q : ObjectProperty D} (e : C ≌ D)

/-- The equivalence of categories between two fullsubcategories `P` and `Q`
of categories `C` and `D` that is induced by an equivalence `e : C ≌ D`
when `Q.inverseImage e.functor = P` and `Q` respects isomorphisms. -/
@[simps]
def congrFullSubcategory [Q.IsClosedUnderIsomorphisms] (h : Q.inverseImage e.functor = P) :
    P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ e.functor) (fun ⟨X, hX⟩ ↦ by rwa [← h] at hX)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun ⟨Y, hY⟩ ↦ by
    rw [← h]
    exact Q.prop_of_iso (e.counitIso.app Y).symm hY)
  unitIso := (P.fullyFaithfulι.whiskeringRight _).preimageIso
    (P.ι.isoWhiskerLeft e.unitIso)
  counitIso := (Q.fullyFaithfulι.whiskeringRight _).preimageIso
    (Q.ι.isoWhiskerLeft e.counitIso)
  functor_unitIso_comp X :=
    ObjectProperty.hom_ext _ (e.functor_unit_comp X.obj)

end Equivalence

end CategoryTheory
