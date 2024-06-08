import Mathlib.CategoryTheory.GroupObjects.GroupObjectFunctor
import Mathlib.CategoryTheory.GroupObjects.StupidLemmas
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Bicategory.Functor

open CategoryTheory Limits

noncomputable section

universe v u

namespace FullSubcategory

variable {C : Type u} [Category.{v,u} C] (P : C → Prop) {X Y : FullSubcategory P} (f : X.1 ≅ Y.1)

@[simp]
def isoOfAmbientIso : X ≅ Y :=
  {hom := f.hom, inv := f.inv, hom_inv_id := f.hom_inv_id, inv_hom_id := f.inv_hom_id}

end FullSubcategory

namespace CategoryTheory.Bicategory

variable (C : Type*) [Category C] (P : C → Prop) (X Y : C) (f : X ≅ Y) (hX : P X) (hY : P Y)

example : (⟨X, hX⟩ : FullSubcategory P) ≅ ⟨Y, hY⟩ := by
  refine {hom := f.hom, inv := f.inv, hom_inv_id := ?_, inv_hom_id := ?_}
  exact f.hom_inv_id
  exact f.inv_hom_id

  instance CatFiniteProducts : Bicategory {C : Cat.{v,u} // HasFiniteProducts C} where
  Hom C D := FullSubcategory (fun (F : C ⥤ D) ↦ Nonempty (PreservesFiniteProducts F))
  id C := ⟨Functor.id C.1, Nonempty.intro inferInstance⟩
  comp F G := ⟨F.1 ⋙ G.1, Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G.1 (Classical.choice F.2) (Classical.choice G.2))⟩
  homCategory C D := FullSubcategory.category (fun F ↦ Nonempty (PreservesFiniteProducts F))
  whiskerLeft := by
    intro C D E F G H α
    exact CategoryTheory.whiskerLeft F.1 (α : G.1 ⟶ H.1)
  whiskerRight α H := CategoryTheory.whiskerRight α H.1
  associator F G H := FullSubcategory.isoOfAmbientIso _ (Functor.associator F.1 G.1 H.1)
  leftUnitor F := FullSubcategory.isoOfAmbientIso _ (Functor.leftUnitor F.1)
  rightUnitor F := FullSubcategory.isoOfAmbientIso _ (Functor.rightUnitor F.1)
  whiskerLeft_id := by
    intro C D E F G
    change CategoryTheory.whiskerLeft F.1 (NatTrans.id G.1) = _
    rw [CategoryTheory.whiskerLeft_id F.1 (G := G.1)]
    rfl
  whiskerLeft_comp := by
    intro C D E F G₁ G₂ G₃ α β
    exact CategoryTheory.whiskerLeft_comp F.1 α β
  id_whiskerLeft := by
    intro C D F G α
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : 𝟭 ↑↑C ⋙ F.obj ⟶ 𝟭 ↑↑C ⋙ G.obj) = _
    ext
    simp only [Functor.comp_obj, Functor.id_obj, whiskerLeft_app]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp]
  comp_whiskerLeft := by
    intro A B C D F G H H' α
    simp only [FullSubcategory.isoOfAmbientIso, whiskerLeft_twice]
    change (_ : (F.1 ⋙ G.1) ⋙ H.1 ⟶ (F.1 ⋙ G.1) ⋙ H'.1) = _
    ext
    simp only [Functor.comp_obj, whiskerLeft_app]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [Functor.associator_hom_app, Functor.associator_inv_app]
    rw [Category.comp_id, Category.id_comp]
    simp only [whiskerLeft_app, Functor.comp_obj]
  id_whiskerRight := by
    intro C D E F G
    exact CategoryTheory.whiskerRight_id' G.1 (G := F.1)
  comp_whiskerRight := by
    intro C D E F G H α β γ
    change (_ : F.obj ⋙ γ.obj ⟶ H.obj ⋙ γ.obj) = _
    ext
    simp only [Functor.comp_obj, whiskerRight_app]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [whiskerRight_app, whiskerRight_app]
    simp only [Functor.map_comp, Functor.comp_obj]
  whiskerRight_id := by
    intro C D F G α
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : F.obj ⋙ 𝟭 ↑↑D ⟶ G.obj ⋙ 𝟭 ↑↑D) = _
    ext
    simp only [Functor.comp_obj, Functor.id_obj, whiskerRight_app, Functor.id_map]
    erw [NatTrans.comp_app, NatTrans.comp_app]
    rw [Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app, Category.comp_id]
    erw [Category.id_comp]
  whiskerRight_comp := by
    intro A B C D F F' α G H
    simp only [FullSubcategory.isoOfAmbientIso, whiskerRight_twice]
    change (_ : F.1 ⋙ G.1 ⋙ H.1 ⟶ F'.1 ⋙ G.1 ⋙ H.1) = _
    ext
    simp only [Functor.comp_obj, whiskerRight_app, Functor.comp_map]
    repeat (erw [NatTrans.comp_app])
    rw [whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
    rw [Category.comp_id, Category.id_comp]
    simp only [Functor.comp_map]
  whisker_assoc := by
    intro A B C D F G G' α H
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : (F.1 ⋙ G.1) ⋙ H.1 ⟶ (F.1 ⋙ G'.1) ⋙ H.1) = _
    ext
    simp only [Functor.comp_obj, whiskerRight_app, whiskerLeft_app]
    repeat (erw [NatTrans.comp_app])
    rw [Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id,
      Category.id_comp]
    simp only [whiskerLeft_app, whiskerRight_app]
  whisker_exchange := by
    intro C D E F F' G G' α β
    change (_ : F.1 ⋙ G.1 ⟶ F'.1 ⋙ G'.1) = _
    ext
    simp only [Functor.comp_obj]
    repeat (erw [NatTrans.comp_app])
    rw [whiskerLeft_app, whiskerRight_app, whiskerRight_app, whiskerLeft_app]
    simp only [Functor.comp_obj, NatTrans.naturality]
  pentagon := by
    intro C₁ C₂ C₃ C₄ C₅ F G H I
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : ((F.1 ⋙ G.1) ⋙ H.1) ⋙ I.1 ⟶ F.1 ⋙ G.1 ⋙ H.1 ⋙ I.1) = _
    exact Functor.pentagon F.1 G.1 H.1 I.1
  triangle := by
    intro C D E F G
    simp only [FullSubcategory.isoOfAmbientIso]
    change (_ : (F.1 ⋙ 𝟭 _) ⋙ G.1 ⟶ F.1 ⋙ G.1) = _
    exact Functor.triangle F.1 G.1

end CategoryTheory.Bicategory

namespace CategoryTheory.GroupObject
open Bicategory

@[simp]
def pseudoFunctor : Pseudofunctor {C : Cat.{v, u} // HasFiniteProducts C} Cat.{v, max v u} where
  obj C := Cat.of (@GroupObject C.1 _ C.2)
  map := by intro C D F
            exact @GroupObjectFunctor.map C.1 _ D.1 _ C.2 D.2 F.1 (Classical.choice F.2)
  map₂ := by
    intro C D F F' α
    exact @GroupObjectFunctor.map₂ C.1 _ D.1 _ C.2 D.2 F.1 F'.1 (Classical.choice F.2)
      (Classical.choice F'.2) α
  mapId C := (@GroupObjectFunctor.mapId C.1 _ C.2 (Classical.choice (Nonempty.intro
    inferInstance)))
  mapComp := by
    intro C D E F G
    simp only
    change @GroupObjectFunctor.map C.1 _ E.1 _ C.2 E.2 (F.1 ⋙ G.1)
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G.1 (Classical.choice F.2) (Classical.choice G.2)))) ≅ _
    exact (@GroupObjectFunctor.mapComp C.1 _ D.1 _ E.1 _ C.2 D.2 E.2 F.1 (Classical.choice F.2)
      G.1 (Classical.choice G.2) (Classical.choice (Nonempty.intro
      (@Limits.compPreservesFiniteProducts _ _ _ _ _ _ F.1 G.1 (Classical.choice F.2)
      (Classical.choice G.2)))))
  map₂_id := by
    intro C D F
    exact @GroupObjectFunctor.map₂_id C.1 _ D.1 _ C.2 D.2 F.1 (Classical.choice F.2)
  map₂_comp := by
    intro C D F F' F'' α α'
    exact @GroupObjectFunctor.map₂_comp C.1 _ D.1 _ C.2 D.2 F.1 F'.1 F''.1
      (Classical.choice F.2) (Classical.choice F'.2) (Classical.choice F''.2) α α'
  map₂_whisker_left := by
    intro C D E F G G' β
    exact @GroupObjectFunctor.map₂_whisker_left C.1 _ D.1 _ E.1 _ C.2 D.2 E.2 F.1
      (Classical.choice F.2) G.1 G'.1 (Classical.choice G.2) (Classical.choice G'.2)
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G.1 (Classical.choice F.2) (Classical.choice G.2))))
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G'.1 (Classical.choice F.2) (Classical.choice G'.2)))) β
  map₂_whisker_right := by
    intro C D E F F' α G
    exact @GroupObjectFunctor.map₂_whisker_right C.1 _ D.1 _ E.1 _ C.2 D.2 E.2 F.1 F'.1
      (Classical.choice F.2) (Classical.choice F'.2) G.1 (Classical.choice G.2)
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G.1 (Classical.choice F.2) (Classical.choice G.2))))
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F'.1 G.1 (Classical.choice F'.2) (Classical.choice G.2)))) α
  map₂_associator := by
    intro A B C D F G H
    exact @GroupObjectFunctor.map₂_associator A.1 _ B.1 _ C.1 _ D.1 _ A.2 B.2 C.2 D.2
      F.1 (Classical.choice F.2) G.1 (Classical.choice G.2) H.1 (Classical.choice H.2)
     (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ G.1 H.1 (Classical.choice G.2) (Classical.choice H.2))))
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 (G.1 ⋙ H.1) (Classical.choice F.2)
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ G.1 H.1 (Classical.choice G.2) (Classical.choice H.2)))))))
       (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 G.1 (Classical.choice F.2) (Classical.choice G.2))))
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ (F.1 ⋙ G.1) H.1 (Classical.choice (Nonempty.intro
      (@Limits.compPreservesFiniteProducts _ _ _ _ _ _ F.1 G.1 (Classical.choice F.2)
      (Classical.choice G.2)))) (Classical.choice H.2))))
  map₂_left_unitor := by
    intro C D F
    exact @GroupObjectFunctor.map₂_left_unitor C.1 _ D.1 _ C.2 D.2 F.1 (Classical.choice F.2)
      (Classical.choice (Nonempty.intro inferInstance))
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ (𝟭 C) F.1 (Classical.choice (Nonempty.intro inferInstance)) (Classical.choice F.2))))
  map₂_right_unitor := by
    intro C D F
    exact @GroupObjectFunctor.map₂_right_unitor C.1 _ D.1 _ C.2 D.2 F.1 (Classical.choice F.2)
      (Classical.choice (Nonempty.intro inferInstance))
      (Classical.choice (Nonempty.intro (@Limits.compPreservesFiniteProducts _ _ _ _
      _ _ F.1 (𝟭 D) (Classical.choice F.2) (Classical.choice (Nonempty.intro inferInstance)))))

end CategoryTheory.GroupObject
