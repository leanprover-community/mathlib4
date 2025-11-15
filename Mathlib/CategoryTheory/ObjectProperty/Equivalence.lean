/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalence of full subcategories

The inclusion functor `P.FullSubcategory ⥤ Q.FullSubcategory` induced
by an inequality `P ≤ Q` in `ObjectProperty C` is an equivalence iff
`Q ≤ P.isoClosure`.

-/

universe v v' u u'

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] {P Q : ObjectProperty C} (h : P ≤ Q)

lemma essSurj_ιOfLE_iff : (ιOfLE h).EssSurj ↔ Q ≤ P.isoClosure := by
  refine ⟨fun _ X hX ↦ ?_, fun hPQ ↦ ⟨fun ⟨Y, hY⟩ ↦ ?_⟩⟩
  · exact ⟨_, ((ιOfLE h).objPreimage ⟨X, hX⟩).2,
      ⟨Q.ι.mapIso ((ιOfLE h).objObjPreimageIso ⟨X, hX⟩).symm⟩⟩
  · obtain ⟨X, hX, ⟨e⟩⟩ := hPQ _ hY
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso e.symm⟩⟩

lemma isEquivalence_ιOfLE_iff : (ιOfLE h).IsEquivalence ↔ Q ≤ P.isoClosure := by
  rw [← essSurj_ιOfLE_iff h]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ { }⟩

instance : (ιOfLE P.le_isoClosure).IsEquivalence := by rw [isEquivalence_ιOfLE_iff]

variable (C) in
/-- The equivalence between the fullsubcategory `⊤` of a category `C` and `C` itself. -/
@[simps]
def topEquivalence : ObjectProperty.FullSubcategory (C := C) ⊤ ≌ C where
  functor := ObjectProperty.ι _
  inverse := ObjectProperty.lift _ (𝟭 _) (by simp)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {P : ObjectProperty C} {Q : ObjectProperty D} (e : C ≌ D)

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
  functor_unitIso_comp X := e.functor_unit_comp X.obj

end CategoryTheory.Equivalence
