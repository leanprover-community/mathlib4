/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Adjoints commute with shifts

-/

namespace CategoryTheory

open Category

/-- Variant of `Iso.ext`. -/
lemma Iso.ext' {C : Type*} [Category C] {X Y : C} {e₁ e₂ : X ≅ Y}
    (h : e₁.inv = e₂.inv) : e₁ = e₂ := by
  change e₁.symm.symm = e₂.symm.symm
  congr 1
  ext
  exact h

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {G₁ G₂ G₃ : C ⥤ D} {F₁ F₂ F₃ : D ⥤ C} (adj₁ : G₁ ⊣ F₁) (adj₂ : G₂ ⊣ F₂) (adj₃ : G₃ ⊣ F₃)

/-- natTransEquiv' -/
@[simps! apply_app symm_apply_app]
def natTransEquiv' : (G₁ ⟶ G₂) ≃ (F₂ ⟶ F₁) where
  toFun α := F₂.rightUnitor.inv ≫ whiskerLeft F₂ adj₁.unit ≫ whiskerLeft _ (whiskerRight α _) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F₁ ≫ F₁.leftUnitor.hom
  invFun β := G₁.leftUnitor.inv ≫ whiskerRight adj₂.unit G₁ ≫ whiskerRight (whiskerLeft _ β ) _ ≫
    (Functor.associator _ _ _ ).hom ≫ whiskerLeft G₂ adj₁.counit ≫ G₂.rightUnitor.hom
  left_inv α := by aesop_cat
  right_inv α := by
    ext X
    dsimp
    simp only [Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc,
      unit_naturality_assoc, right_triangle_components_assoc, ← α.naturality]

@[simp]
lemma natTransEquiv_id : natTransEquiv' adj₁ adj₁ (𝟙 _) = 𝟙 _ := by aesop_cat

@[simp]
lemma natTransEquiv_symm_id : (natTransEquiv' adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by aesop_cat

@[reassoc (attr := simp)]
lemma natTransEquiv_comp (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃) :
    natTransEquiv' adj₂ adj₃ β ≫ natTransEquiv' adj₁ adj₂ α =
      natTransEquiv' adj₁ adj₃ (α ≫ β) := by
  ext X
  apply (adj₁.homEquiv _ _).symm.injective
  dsimp
  simp [homEquiv_counit]

@[reassoc (attr := simp)]
lemma natTransEquiv_symm_comp (α : F₃ ⟶ F₂) (β : F₂ ⟶ F₁) :
    (natTransEquiv' adj₁ adj₂).symm β ≫ (natTransEquiv' adj₂ adj₃).symm α =
      (natTransEquiv' adj₁ adj₃).symm (α ≫ β) := by
  obtain ⟨α', rfl⟩ := (natTransEquiv' adj₂ adj₃).surjective α
  obtain ⟨β', rfl⟩ := (natTransEquiv' adj₁ adj₂).surjective β
  simp

/-- natIsoEquiv' -/
@[simps]
def natIsoEquiv' : (G₁ ≅ G₂) ≃ (F₁ ≅ F₂) where
  toFun e :=
    { hom := natTransEquiv' adj₂ adj₁ e.inv
      inv := natTransEquiv' adj₁ adj₂ e.hom }
  invFun e :=
    { hom := (natTransEquiv' adj₁ adj₂).symm e.inv
      inv := (natTransEquiv' adj₂ adj₁).symm e.hom }
  left_inv e := by dsimp; ext1; simp only [Equiv.symm_apply_apply]
  right_inv e := by dsimp; ext1; simp only [Equiv.apply_symm_apply]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (A Z : Type*) [AddMonoid A] [AddGroup Z]
  [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]
  [HasShift C Z] [HasShift D Z]

variable {A}

abbrev compat_unit (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a) :=
  ∀ (X : C),
  (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app (F.obj X)

abbrev compat_counit (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a) :=
  ∀ (Y : D),
  adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app (G.obj Y) ≫ (adj.counit.app Y)⟦a⟧'

lemma compat_unit_to_counit (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a) (h : adj.compat_unit a e₁ e₂) :
    adj.compat_counit a e₁ e₂ := by
  intro Y
  have eq := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _))] at eq
  dsimp at eq ⊢
  conv_rhs at eq => slice 3 4; rw [Iso.hom_inv_id_app]
  conv_rhs at eq => erw [id_comp]; rw [← Functor.map_comp, Iso.hom_inv_id_app];
                    erw [Functor.map_id]; rw [comp_id]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp, adj.unit_naturality_assoc, ← eq]
  slice_rhs 4 5 => rw [← Functor.map_comp, ← assoc, Iso.inv_hom_id_app]; erw [id_comp]
  erw [← e₂.inv.naturality]; rw [← assoc _ _ (e₂.inv.app Y), Functor.comp_map, ← Functor.map_comp]
  simp only [Functor.id_obj, Functor.comp_obj, right_triangle_components, Functor.map_id, id_comp,
    Iso.hom_inv_id_app]

lemma compat_unit_right (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a) (h : adj.compat_unit a e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc, ← this, assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

lemma compat_counit_left (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a) (h : adj.compat_counit a e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _)), ← assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id,
    id_comp] at this
  rw [this]
  erw [e₁.hom.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp, left_triangle_components]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_id, comp_id]

lemma compat_unique_right (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (h : adj.compat_unit a e₁ e₂) (h' : adj.compat_unit a e₁ e₂') : e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext _
  rw [Iso.symm_hom, Iso.symm_hom, adj.compat_unit_right a e₁ e₂ h,
    adj.compat_unit_right a e₁ e₂' h']

lemma compat_unique_left (a : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (h : adj.compat_unit a e₁ e₂) (h' : adj.compat_unit a e₁' e₂) : e₁ = e₁' := by
  ext _
  rw [adj.compat_counit_left a e₁ e₂ (adj.compat_unit_to_counit a e₁ e₂ h),
    adj.compat_counit_left a e₁' e₂ (adj.compat_unit_to_counit a e₁' e₂ h')]

lemma compat_unit_isoZero : adj.compat_unit 0 (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro X
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app, Functor.map_comp,
    assoc, unit_naturality_assoc]
  slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app _)]
  simp only [Functor.id_obj, NatTrans.naturality, Functor.id_map, Functor.map_id, id_comp, assoc,
    Iso.inv_hom_id_app, comp_id]

lemma compat_unit_add (a b : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)
    (h : adj.compat_unit a e₁ e₂) (h' : adj.compat_unit b e₁' e₂') :
    adj.compat_unit (a + b) (Functor.CommShift.isoAdd e₁ e₁') (Functor.CommShift.isoAdd e₂ e₂') :=
  by
  intro X
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app, Functor.map_comp,
    assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  slice_rhs 4 5 => erw [e₂'.hom.naturality]
  have := h' (X⟦a⟧)
  rw [← cancel_mono (e₂'.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  simp only [Functor.id_obj, Functor.comp_obj, comp_id] at this
  slice_rhs 2 3 => rw [← this]
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.comp_map]
  rw [← cancel_mono ((shiftFunctorAdd C a b).hom.app _), assoc, assoc, assoc, assoc,
    Iso.inv_hom_id_app]; erw [comp_id]
  rw [← (shiftFunctor C b).map_comp, ← (shiftFunctor C b).map_comp, ← h X]
  simp only [Functor.comp_obj, NatTrans.naturality, Functor.comp_map, Functor.id_obj]


variable (A)

class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

namespace CommShift

attribute [instance] commShift_unit commShift_counit

/-- Constructor for `Adjunction.CommShift`. -/
lemma mk' (h : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
  commShift_counit := ⟨by
    intro a
    ext X
    have eq := NatTrans.CommShift.app_shift adj.unit a (F.obj X)
    dsimp at eq ⊢
    simp only [Functor.commShiftIso_id_hom_app, Functor.comp_obj,
      Functor.id_obj, Functor.commShiftIso_comp_inv_app, id_comp,
      Functor.commShiftIso_comp_hom_app, assoc, comp_id] at eq ⊢
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit, F.map_comp]
    dsimp
    rw [adj.unit_naturality_assoc]
    simp only [eq, assoc, ← F.map_comp, Iso.inv_hom_id_app_assoc, right_triangle_components,
      ← F.commShiftIso_inv_naturality, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
      Iso.hom_inv_id_app, Functor.comp_obj]⟩

end CommShift

variable {A}

@[reassoc]
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        F.map ((G.commShiftIso a).hom.app X) ≫
          (F.commShiftIso a).hom.app (G.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.CommShift.comm_app adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (X : D) :
    (adj.counit.app X)⟦a⟧' =
      (G.commShiftIso a).inv.app (F.obj X) ≫ G.map ((F.commShiftIso a).inv.app X)
        ≫ adj.counit.app (X⟦a⟧) := by
  have eq := NatTrans.CommShift.comm_app adj.counit a X
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.CommShift.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]
