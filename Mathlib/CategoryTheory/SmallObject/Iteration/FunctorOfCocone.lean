/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# The functor from `Set.Iic j` deduced from a cocone

Given a functor `F : Set.Iio j ⥤ C` and `c : Cocone F`, we define
an extension of `F` as a functor `Set.Iic j ⥤ C` for which
the top element is mapped to `c.pt`.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Category Limits

namespace SmallObject

namespace SuccStruct

variable {C : Type*} [Category* C]
  {J : Type u} [LinearOrder J]
  {j : J} {F : Set.Iio j ⥤ C} (c : Cocone F)

namespace ofCocone

/-- Auxiliary definition for `ofCocone`. -/
def obj (i : J) : C :=
  if hi : i < j then
    F.obj ⟨i, hi⟩
  else c.pt

/-- Auxiliary definition for `ofCocone`. -/
def objIso (i : J) (hi : i < j) :
    obj c i ≅ F.obj ⟨i, hi⟩ :=
  eqToIso (dif_pos hi)

/-- Auxiliary definition for `ofCocone`. -/
def objIsoPt :
    obj c j ≅ c.pt :=
  eqToIso (dif_neg (by simp))

/-- Auxiliary definition for `ofCocone`. -/
def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    obj c i₁ ⟶ obj c i₂ :=
  if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt hi h₂)).hom ≫ F.map (homOfLE hi) ≫ (objIso c i₂ h₂).inv
  else
    have h₂' : i₂ = j := le_antisymm hi₂ (by simpa using h₂)
    if h₁ : i₁ < j then
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫ (objIsoPt c).inv ≫ eqToHom (by subst h₂'; rfl)
    else
      have h₁' : i₁ = j := le_antisymm (hi.trans hi₂) (by simpa using h₁)
      eqToHom (by subst h₁' h₂'; rfl)

lemma map_id (i : J) (hi : i ≤ j) :
    map c i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  grind

set_option backward.defeqAttrib.useBackward true in
lemma map_comp (i₁ i₂ i₃ : J) (hi : i₁ ≤ i₂) (hi' : i₂ ≤ i₃) (hi₃ : i₃ ≤ j) :
    map c i₁ i₃ (hi.trans hi') hi₃ =
      map c i₁ i₂ hi (hi'.trans hi₃) ≫
        map c i₂ i₃ hi' hi₃ := by
  obtain hi₁₂ | rfl := hi.lt_or_eq
  · obtain hi₂₃ | rfl := hi'.lt_or_eq
    · dsimp [map]
      obtain hi₃' | rfl := hi₃.lt_or_eq
      · rw [dif_pos hi₃', dif_pos (hi₂₃.trans hi₃'), dif_pos hi₃', assoc, assoc,
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
      · rw [dif_neg (by simp), dif_pos (hi₁₂.trans hi₂₃), dif_pos hi₂₃, dif_neg (by simp),
          dif_pos hi₂₃, eqToHom_refl, comp_id, assoc, assoc, Iso.inv_hom_id_assoc,
          Cocone.w_assoc]
    · rw [map_id, comp_id]
  · rw [map_id, id_comp]

end ofCocone

/-- Given a functor `F : Set.Iio j ⥤ C` and a cocone `c : Cocone F`,
where `j : J` and `J` is linearly ordered, this is the functor
`Set.Iic j ⥤ C` which extends `F` and sends the top element to `c.pt`. -/
def ofCocone : Set.Iic j ⥤ C where
  obj i := ofCocone.obj c i.1
  map {_ j} f := ofCocone.map c _ _ (leOfHom f) j.2
  map_id i := ofCocone.map_id _ _ i.2
  map_comp {_ _ i₃} _ _ := ofCocone.map_comp _ _ _ _ _ _ i₃.2

lemma ofCocone_obj_eq (i : J) (hi : i < j) :
    (ofCocone c).obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩ :=
  dif_pos hi

/-- The isomorphism `(ofCocone c).obj ⟨i, _⟩ ≅ F.obj ⟨i, _⟩` when `i < j`. -/
def ofCoconeObjIso (i : J) (hi : i < j) :
    (ofCocone c).obj ⟨i, hi.le⟩ ≅ F.obj ⟨i, hi⟩ :=
  ofCocone.objIso c _ _

lemma ofCocone_obj_eq_pt :
    (ofCocone c).obj ⟨j, by simp⟩ = c.pt :=
  dif_neg (by simp)

/-- The isomorphism `(ofCocone c).obj ⟨j, _⟩ ≅ c.pt`. -/
def ofCoconeObjIsoPt :
    (ofCocone c).obj ⟨j, by simp⟩ ≅ c.pt :=
  ofCocone.objIsoPt c

lemma ofCocone_map_to_top (i : J) (hi : i < j) :
    (ofCocone c).map (homOfLE hi.le) =
      (ofCoconeObjIso c i hi).hom ≫ c.ι.app ⟨i, hi⟩ ≫ (ofCoconeObjIsoPt c).inv := by
  dsimp [ofCocone, ofCocone.map, ofCoconeObjIso, ofCoconeObjIsoPt]
  rw [dif_neg (by simp), dif_pos hi, comp_id]

@[reassoc]
lemma ofCocone_map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ < j) :
    (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) =
      (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) ≫
        (ofCoconeObjIso c i₂ hi₂).inv := by
  dsimp [ofCocone, ofCoconeObjIso, ofCocone.map]
  rw [dif_pos hi₂]

@[reassoc]
lemma ofCoconeObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ < j) :
    (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) ≫
      (ofCoconeObjIso c i₂ hi₂).hom =
      (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) := by
  rw [ofCocone_map c i₁ i₂ hi hi₂, assoc, assoc, Iso.inv_hom_id, comp_id]

/-- The isomorphism expressing that `ofCocone c` extends the functor `F`
when `c : Cocone F`. -/
@[simps!]
def restrictionLTOfCoconeIso :
    SmallObject.restrictionLT (ofCocone c) (le_refl j) ≅ F :=
  NatIso.ofComponents (fun ⟨i, hi⟩ ↦ ofCoconeObjIso c i hi)
    (by intros; apply ofCoconeObjIso_hom_naturality)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {c} in
/-- If `c` is a colimit cocone, then so is `coconeOfLE (ofCocone c) (le_refl j)`. -/
def isColimitCoconeOfLEOfCocone (hc : IsColimit c) :
    IsColimit (coconeOfLE (ofCocone c) (le_refl j)) :=
  (IsColimit.precomposeInvEquiv (restrictionLTOfCoconeIso c) _).1
    (IsColimit.ofIsoColimit hc
      (Cocone.ext (ofCoconeObjIsoPt c).symm (fun ⟨i, hi⟩ ↦ by
        dsimp
        rw [ofCocone_map_to_top _ _ hi, Iso.inv_hom_id_assoc])))

lemma arrowMap_ofCocone (i₁ i₂ : J) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    arrowMap (ofCocone c) i₁ i₂ h₁₂ h₂.le =
      Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, lt_of_le_of_lt h₁₂ h₂⟩ ⟶ ⟨i₂, h₂⟩)) :=
  Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq _ _ _) (ofCocone_map _ _ _ _ _)

lemma arrowMap_ofCocone_to_top (i : J) (hi : i < j) :
    arrowMap (ofCocone c) i j hi.le (by simp) = Arrow.mk (c.ι.app ⟨i, hi⟩) := by
  rw [arrowMap, ofCocone_map_to_top _ _ hi]
  exact Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq_pt _) rfl

end SuccStruct

end SmallObject

end CategoryTheory
