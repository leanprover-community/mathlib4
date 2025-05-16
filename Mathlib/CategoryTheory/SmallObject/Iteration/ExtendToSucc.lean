/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# Extension of a functor from `Set.Iic j` to `Set.Iic (Order.succ j)`

Given a linearly ordered type `J` with `SuccOrder J`, `j : J` that is not maximal,
we define the extension of a functor `F : Set.Iic j ⥤ C` as a
functor `Set.Iic (Order.succ j) ⥤ C` when an object `X : C` and a morphism
`τ : F.obj ⟨j, _⟩ ⟶ X` is given.

-/

universe u

namespace CategoryTheory

open Category

namespace SmallObject

variable {C : Type*} [Category C]
  {J : Type u} [LinearOrder J] [SuccOrder J] {j : J} (hj : ¬IsMax j)
  (F : Set.Iic j ⥤ C) {X : C} (τ : F.obj ⟨j, by simp⟩ ⟶ X)

namespace SuccStruct

namespace extendToSucc

variable (X)

/-- `extendToSucc`, on objects: it coincides with `F.obj` for `i ≤ j`, and
it sends `Order.succ j` to the given object `X`. -/
def obj (i : Set.Iic (Order.succ j)) : C :=
  if hij : i.1 ≤ j then F.obj ⟨i.1, hij⟩ else X

lemma obj_eq (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i := dif_pos i.2

/-- The isomorphism `obj F X ⟨i, _⟩ ≅ F.obj i` when `i : Set.Iic j`. -/
def objIso (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj i :=
  eqToIso (obj_eq _ _ _)

include hj in
lemma obj_succ_eq : obj F X ⟨Order.succ j, by simp⟩ = X :=
  dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj)

/-- The isomorphism `obj F X ⟨Order.succ j, _⟩ ≅ X`. -/
def objSuccIso :
    obj F X ⟨Order.succ j, by simp⟩ ≅ X :=
  eqToIso (obj_succ_eq hj _ _)

variable {X}

/-- `extendToSucc`, on morphisms. -/
def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ Order.succ j) :
    obj F X ⟨i₁, hi.trans hi₂⟩ ⟶ obj F X ⟨i₂, hi₂⟩ :=
  if h₁ : i₂ ≤ j then
    (objIso F X ⟨i₁, hi.trans h₁⟩).hom ≫ F.map (homOfLE hi) ≫ (objIso F X ⟨i₂, h₁⟩).inv
  else
    if h₂ : i₁ ≤ j then
      (objIso F X ⟨i₁, h₂⟩).hom ≫ F.map (homOfLE h₂) ≫ τ ≫
        (objSuccIso hj F X).inv ≫ eqToHom (by
          congr
          exact le_antisymm (Order.succ_le_of_lt (not_le.1 h₁)) hi₂)
    else
      eqToHom (by
        congr
        rw [le_antisymm hi₂ (Order.succ_le_of_lt (not_le.1 h₁)),
          le_antisymm (hi.trans hi₂) (Order.succ_le_of_lt (not_le.1 h₂))])

lemma map_eq (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    map hj F τ i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      (objIso F X ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homOfLE hi) ≫
        (objIso F X ⟨i₂, hi₂⟩).inv :=
  dif_pos hi₂

lemma map_self_succ :
    map hj F τ j (Order.succ j) (Order.le_succ j) (by rfl) =
      (objIso F X ⟨j, by simp⟩).hom ≫ τ ≫ (objSuccIso hj F X).inv := by
  dsimp [map]
  rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
    dif_pos (by rfl), Functor.map_id, comp_id, id_comp]

@[simp]
lemma map_id (i : J) (hi : i ≤ Order.succ j) :
    map hj F τ i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  by_cases h₁ : i ≤ j
  · rw [dif_pos h₁, CategoryTheory.Functor.map_id, id_comp, Iso.hom_inv_id]
  · obtain rfl : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (not_le.1 h₁))
    rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
      dif_neg h₁]

lemma map_comp (i₁ i₂ i₃ : J) (h₁₂ : i₁ ≤ i₂) (h₂₃ : i₂ ≤ i₃) (h : i₃ ≤ Order.succ j) :
    map hj F τ i₁ i₃ (h₁₂.trans h₂₃) h =
      map hj F τ i₁ i₂ h₁₂ (h₂₃.trans h) ≫ map hj F τ i₂ i₃ h₂₃ h := by
  by_cases h₁ : i₃ ≤ j
  · rw [map_eq hj F τ i₁ i₂ _ (h₂₃.trans h₁), map_eq hj F τ i₂ i₃ _ h₁,
      map_eq hj F τ i₁ i₃ _ h₁, assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain rfl : i₃ = Order.succ j := le_antisymm h (Order.succ_le_of_lt (not_le.1 h₁))
    obtain h₂ | rfl := h₂₃.lt_or_eq
    · rw [Order.lt_succ_iff_of_not_isMax hj] at h₂
      rw [map_eq hj F τ i₁ i₂ _ h₂]
      dsimp [map]
      rw [dif_neg h₁, dif_pos (h₁₂.trans h₂), dif_neg h₁, dif_pos h₂, assoc, assoc,
        Iso.inv_hom_id_assoc,comp_id, ← Functor.map_comp_assoc, homOfLE_comp]
    · rw [map_id, comp_id]

end extendToSucc

open extendToSucc in
include hj in
/-- The extension to `Set.Iic (Order.succ j) ⥤ C` of a functor `F : Set.Iic j ⥤ C`,
when we specify a morphism `F.obj ⟨j, _⟩ ⟶ X`. -/
def extendToSucc : Set.Iic (Order.succ j) ⥤ C where
  obj := obj F X
  map {i₁ i₂} f := map hj F τ i₁ i₂ (leOfHom f) i₂.2
  map_id _ := extendToSucc.map_id _ F τ _ _
  map_comp {i₁ i₂ i₃} f g := extendToSucc.map_comp hj F τ i₁ i₂ i₃ (leOfHom f) (leOfHom g) i₃.2

lemma extendToSucc_obj_eq (i : J) (hi : i ≤ j) :
    (extendToSucc hj F τ).obj ⟨i, hi.trans (Order.le_succ j)⟩ = F.obj ⟨i, hi⟩ :=
  extendToSucc.obj_eq F X ⟨i, hi⟩

/-- The isomorphism `(extendToSucc hj F τ).obj ⟨i, _⟩ ≅ F.obj i` when `i ≤ j` -/
def extendToSuccObjIso (i : J) (hi : i ≤ j) :
    (extendToSucc hj F τ).obj ⟨i, hi.trans (Order.le_succ j)⟩ ≅ F.obj ⟨i, hi⟩ :=
  extendToSucc.objIso F X ⟨i, hi⟩

lemma extendToSucc_obj_succ_eq :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ = X :=
  extendToSucc.obj_succ_eq hj F X

/-- The isomorphism `(extendToSucc hj F τ).obj ⟨Order.succ j, _⟩ ≅ X`. -/
def extendToSuccObjSuccIso :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ ≅ X :=
  extendToSucc.objSuccIso hj F X

@[reassoc]
lemma extendToSuccObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) ≫
    (extendToSuccObjIso hj F τ i₂ hi₂).hom =
      (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi) := by
  dsimp [extendToSucc, extendToSuccObjIso]
  rw [extendToSucc.map_eq _ _ _ _ _ _ hi₂, assoc, assoc, Iso.inv_hom_id, comp_id]

/-- The isomorphism expressing that `extendToSucc hj F τ` extends `F`. -/
@[simps!]
def extendToSuccRestrictionLEIso :
    SmallObject.restrictionLE (extendToSucc hj F τ) (Order.le_succ j) ≅ F :=
  NatIso.ofComponents (fun i ↦ extendToSuccObjIso hj F τ i.1 i.2) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    apply extendToSuccObjIso_hom_naturality)

lemma extendToSucc_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) =
      (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi) ≫
      (extendToSuccObjIso hj F τ i₂ hi₂).inv := by
  rw [← extendToSuccObjIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]

lemma extendToSucc_map_le_succ :
    (extendToSucc hj F τ).map (homOfLE (Order.le_succ j)) =
        (extendToSuccObjIso hj F τ j (by simp)).hom ≫ τ ≫
          (extendToSuccObjSuccIso hj F τ).inv :=
  extendToSucc.map_self_succ _ _ _

lemma arrowMap_extendToSucc (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    arrowMap (extendToSucc hj F τ) i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      arrowMap F i₁ i₂ hi hi₂ := by
  simp [arrowMap, extendToSucc_map hj F τ i₁ i₂ hi hi₂,
    extendToSuccObjIso, extendToSucc.objIso]

lemma arrowSucc_extendToSucc :
    arrowSucc (extendToSucc hj F τ) j (Order.lt_succ_of_not_isMax hj) =
      Arrow.mk τ := by
  simp [arrowSucc, arrowMap, extendToSucc_map_le_succ, extendToSuccObjIso,
    extendToSucc.objIso, extendToSuccObjSuccIso, extendToSucc.objSuccIso]

end SuccStruct

end SmallObject

end CategoryTheory
