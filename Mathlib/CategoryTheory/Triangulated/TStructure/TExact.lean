/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc

/-!
# t-exact functors

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Triangulated Pretriangulated

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Functor

variable (F : C ⥤ D) [F.CommShift ℤ] (t₁ : TStructure C) (t₂ : TStructure D)

class RightTExact [F.IsTriangulated] : Prop where
  objGE (X : C) (n : ℤ) [t₁.IsGE X n] : t₂.IsGE (F.obj X) n

class LeftTExact [F.IsTriangulated] : Prop where
  objLE (X : C) (n : ℤ) [t₁.IsLE X n] : t₂.IsLE (F.obj X) n

variable [F.IsTriangulated]

lemma isGE_obj (X : C) (n : ℤ) [t₁.IsGE X n] [h : F.RightTExact t₁ t₂] : t₂.IsGE (F.obj X) n :=
  h.objGE X n

lemma isLE_obj (X : C) (n : ℤ) [t₁.IsLE X n] [h : F.LeftTExact t₁ t₂] : t₂.IsLE (F.obj X) n :=
  h.objLE X n

class TExact : Prop where
  rightTExact : F.RightTExact t₁ t₂
  leftTExact : F.LeftTExact t₁ t₂

attribute [instance] TExact.rightTExact TExact.leftTExact

/-- Constructor for `RightTExact`. -/
lemma RightTExact.mk' (h : ∀ (X : C) [t₁.IsGE X 0], t₂.IsGE (F.obj X) 0) :
    F.RightTExact t₁ t₂ where
  objGE X n _ := by
    have := t₁.isGE_shift X n n 0 (add_zero n)
    have : t₂.IsGE ((shiftFunctor C n ⋙ F).obj X) 0 := h (X⟦n⟧)
    have : t₂.IsGE ((F.obj X)⟦n⟧) 0 := t₂.isGE_of_iso ((F.commShiftIso n).app X) 0
    exact t₂.isGE_of_shift (F.obj X) n n 0 (add_zero n)

/-- Constructor for `LeftTExact`. -/
lemma LeftTExact.mk' (h : ∀ (X : C) [t₁.IsLE X 0], t₂.IsLE (F.obj X) 0) :
    F.LeftTExact t₁ t₂ where
  objLE X n _ := by
    have := t₁.isLE_shift X n n 0 (add_zero n)
    have : t₂.IsLE ((shiftFunctor C n ⋙ F).obj X) 0 := h (X⟦n⟧)
    have : t₂.IsLE ((F.obj X)⟦n⟧) 0 := t₂.isLE_of_iso ((F.commShiftIso n).app X) 0
    exact t₂.isLE_of_shift (F.obj X) n n 0 (add_zero n)

section

variable [h : F.RightTExact t₁ t₂]

set_option backward.isDefEq.respectTransparency false in
noncomputable def truncGEComparison (n : ℤ) : F ⋙ t₂.truncGE n ⟶ t₁.truncGE n ⋙ F where
  app X :=
    have := h.objGE ((t₁.truncGE n).obj X) n
    t₂.descTruncGE (F.map ((t₁.truncGEπ n).app X)) n
  naturality {X Y} f := by
    have := h.objGE ((t₁.truncGE n).obj X) n
    have := h.objGE ((t₁.truncGE n).obj Y) n
    dsimp
    apply t₂.from_truncGE_obj_ext
    dsimp
    rw [TStructure.π_descTruncGE_assoc]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [TStructure.π_descTruncGE, ← F.map_comp, ← F.map_comp, ← NatTrans.naturality]
    rfl

@[reassoc (attr := simp)]
lemma truncGEComparison_app_fac (X : C) (n : ℤ) :
    (t₂.truncGEπ n).app (F.obj X) ≫ (truncGEComparison F t₁ t₂ n).app X =
      F.map ((t₁.truncGEπ n).app X) := by
  dsimp
  have := h.objGE ((t₁.truncGE n).obj X) n
  apply t₂.π_descTruncGE

end

section

variable [h : F.LeftTExact t₁ t₂]

set_option backward.isDefEq.respectTransparency false in
noncomputable def truncLEComparison (n : ℤ) : t₁.truncLE n ⋙ F ⟶ F ⋙ t₂.truncLE n where
  app X :=
    have := h.objLE ((t₁.truncLE n).obj X) n
    t₂.liftTruncLE (F.map ((t₁.truncLEι n).app X)) n
  naturality {X Y} f := by
    have := h.objLE ((t₁.truncLE n).obj X) n
    have := h.objLE ((t₁.truncLE n).obj Y) n
    dsimp
    apply t₂.to_truncLE_obj_ext
    dsimp
    simp only [Category.assoc, TStructure.liftTruncLE_ι, NatTrans.naturality, id_obj, id_map,
      TStructure.liftTruncLE_ι_assoc, ← F.map_comp]

@[reassoc (attr := simp)]
lemma truncLEComparison_app_fac (X : C) (n : ℤ) :
    (truncLEComparison F t₁ t₂ n).app X ≫ (t₂.truncLEι n).app (F.obj X) =
      F.map ((t₁.truncLEι n).app X) := by
  dsimp
  have := h.objLE ((t₁.truncLE n).obj X) n
  apply t₂.liftTruncLE_ι

end

variable [h : F.TExact t₁ t₂]

namespace TExact

set_option backward.isDefEq.respectTransparency false in
def triangleGELEIso_aux (a b : ℤ) (h : a + 1 = b) (X : C) :
  ∃ (e : (t₂.triangleLEGE a b h).obj (F.obj X) ≅
    F.mapTriangle.obj ((t₁.triangleLEGE a b h).obj X))
      (_ : e.inv.hom₁ = (F.truncLEComparison t₁ t₂ a).app X)
      (_ : e.hom.hom₃ = (F.truncGEComparison t₁ t₂ b).app X),
      e.hom.hom₂ = 𝟙 _ := by
  have : t₂.IsLE (F.mapTriangle.obj ((t₁.triangleLEGE a b h).obj X)).obj₁ a := by
    dsimp
    apply F.isLE_obj t₁ t₂
  have : t₂.IsGE (F.mapTriangle.obj ((t₁.triangleLEGE a b h).obj X)).obj₃ b := by
    dsimp
    apply F.isGE_obj t₁ t₂
  obtain ⟨e, h₂⟩ := t₂.triangle_iso_exists
    (t₂.triangleLEGE_distinguished a b h (F.obj X))
    (F.map_distinguished _ (t₁.triangleLEGE_distinguished a b h X)) (Iso.refl _) a b
    (by dsimp; infer_instance) (by dsimp; infer_instance) inferInstance inferInstance
  dsimp at h₂
  have h₂' : e.inv.hom₂ = 𝟙 _ := by
    rw [← cancel_mono e.hom.hom₂, Iso.inv_hom_id_triangle_hom₂, h₂]
    dsimp
    rw [comp_id]
  refine ⟨e, ?_, ?_, h₂⟩
  · apply t₂.to_truncLE_obj_ext
    simpa [h₂'] using e.inv.comm₁.symm
  · apply t₂.from_truncGE_obj_ext
    simpa [h₂] using e.hom.comm₂

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) (X : C) : IsIso ((truncGEComparison F t₁ t₂ n).app X) := by
  obtain ⟨e, _, h₃, _⟩ := triangleGELEIso_aux F t₁ t₂ (n-1) n (by lia) X
  rw [← h₃]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance (n : ℤ) (X : C) : IsIso ((truncLEComparison F t₁ t₂ n).app X) := by
  obtain ⟨e, h₁, _, _⟩ := triangleGELEIso_aux F t₁ t₂ n (n + 1) (by lia) X
  rw [← h₁]
  infer_instance

instance (n : ℤ) : IsIso (truncGEComparison F t₁ t₂ n) :=
  NatIso.isIso_of_isIso_app _
instance (n : ℤ) : IsIso (truncLEComparison F t₁ t₂ n) :=
  NatIso.isIso_of_isIso_app _


end TExact

@[simps! hom]
noncomputable def truncGEIso (n : ℤ) : F ⋙ t₂.truncGE n ≅ t₁.truncGE n ⋙ F :=
    asIso (F.truncGEComparison t₁ t₂ n)

@[reassoc (attr := simp)]
lemma truncGEIso_hom_inv_id_app (X : C) (n : ℤ) :
    (F.truncGEComparison t₁ t₂ n).app X ≫ (F.truncGEIso t₁ t₂ n).inv.app X = 𝟙 _ :=
  (F.truncGEIso t₁ t₂ n).hom_inv_id_app X

@[reassoc (attr := simp)]
lemma truncGEIso_inv_hom_id_app (X : C) (n : ℤ) :
    (F.truncGEIso t₁ t₂ n).inv.app X ≫ (F.truncGEComparison t₁ t₂ n).app X = 𝟙 _ :=
  (F.truncGEIso t₁ t₂ n).inv_hom_id_app X

@[simps! hom]
noncomputable def truncLEIso (n : ℤ) : t₁.truncLE n ⋙ F ≅ F ⋙ t₂.truncLE n :=
    asIso (F.truncLEComparison t₁ t₂ n)

@[reassoc (attr := simp)]
lemma truncLEIso_hom_inv_id_app (X : C) (n : ℤ) :
    (F.truncLEComparison t₁ t₂ n).app X ≫ (F.truncLEIso t₁ t₂ n).inv.app X = 𝟙 _ :=
  (F.truncLEIso t₁ t₂ n).hom_inv_id_app X

@[reassoc (attr := simp)]
lemma truncLEIso_inv_hom_id_app (X : C) (n : ℤ) :
    (F.truncLEIso t₁ t₂ n).inv.app X ≫ (F.truncLEComparison t₁ t₂ n).app X = 𝟙 _ :=
  (F.truncLEIso t₁ t₂ n).inv_hom_id_app X

set_option backward.isDefEq.respectTransparency false in
noncomputable def triangleLEGEIso (a b : ℤ) (h : a + 1 = b) :
    F ⋙ t₂.triangleLEGE a b h ≅ t₁.triangleLEGE a b h ⋙ F.mapTriangle :=
  Pretriangulated.Triangle.functorIsoMk _ _ (F.truncLEIso t₁ t₂ a).symm (Iso.refl _)
    (F.truncGEIso t₁ t₂ b) (by
      ext X
      dsimp
      rw [← cancel_epi ((F.truncLEIso t₁ t₂ a).hom.app X)]
      simp) (by aesop_cat) (by
      ext X
      dsimp
      obtain ⟨e, h₁, h₃, _⟩ := TExact.triangleGELEIso_aux F t₁ t₂ a b h X
      have h₁' : e.hom.hom₁ = (F.truncLEIso t₁ t₂ a).inv.app X := by
        rw [← cancel_mono e.inv.hom₁, ← comp_hom₁, e.hom_inv_id, id_hom₁,
          h₁, truncLEIso_inv_hom_id_app]
        rfl
      rw [← h₁', ← h₃]
      exact e.hom.comm₃)

noncomputable def truncLEGEIso (a b : ℤ) : t₁.truncLEGE a b ⋙ F ≅ F ⋙ t₂.truncLEGE a b :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft (t₁.truncGE a) (F.truncLEIso t₁ t₂ b) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (F.truncGEIso t₁ t₂ a).symm (t₂.truncLE b) ≪≫ Functor.associator _ _ _

noncomputable def truncGELEIso (a b : ℤ) : t₁.truncGELE a b ⋙ F ≅ F ⋙ t₂.truncGELE a b :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (t₁.truncLE b) (F.truncGEIso t₁ t₂ a).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (F.truncLEIso t₁ t₂ b) (t₂.truncGE a) ≪≫ Functor.associator _ _ _

end Functor

end CategoryTheory
