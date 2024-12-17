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

/-
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
-/

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]

namespace CommShift

variable (a b : A) (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (f₁ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (f₂ : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)

abbrev compat_unit :=
  ∀ (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

abbrev compat_counit :=
  ∀ (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

lemma compat_counit_of_compat_unit (h : compat_unit adj a e₁ e₂) : compat_counit adj a e₁ e₂ := by
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

lemma compat_unit_right (h : compat_unit adj a e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc, ← this, assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

lemma compat_counit_left (h : compat_counit adj a e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _)), ← assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id,
    id_comp] at this
  rw [this]
  erw [e₁.hom.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp, left_triangle_components]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_id, comp_id]

lemma compat_unit_unique_right (h : compat_unit adj a e₁ e₂) (h' : compat_unit adj a e₁ e₂') :
    e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext _
  rw [Iso.symm_hom, Iso.symm_hom, compat_unit_right adj a e₁ e₂ h,
    compat_unit_right adj a e₁ e₂' h']

lemma compat_counit_unique_left (h : compat_counit adj a e₁ e₂) (h' : compat_counit adj a e₁' e₂) :
    e₁ = e₁' := by
  ext _
  rw [compat_counit_left adj a e₁ e₂ h, compat_counit_left adj a e₁' e₂ h']

lemma compat_unit_isoZero : compat_unit adj 0 (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro _
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app, Functor.map_comp,
    assoc, unit_naturality_assoc]
  slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app _)]
  simp only [Functor.id_obj, NatTrans.naturality, Functor.id_map, Functor.map_id, id_comp, assoc,
    Iso.inv_hom_id_app, comp_id]

lemma compat_unit_isoAdd (h : compat_unit adj a e₁ e₂) (h' : compat_unit adj b f₁ f₂) :
    compat_unit adj (a + b) (Functor.CommShift.isoAdd e₁ f₁) (Functor.CommShift.isoAdd e₂ f₂) := by
  intro X
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app, Functor.map_comp,
    assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  slice_rhs 4 5 => erw [f₂.hom.naturality]
  have := h' (X⟦a⟧)
  rw [← cancel_mono (f₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  simp only [Functor.id_obj, Functor.comp_obj, comp_id] at this
  slice_rhs 2 3 => rw [← this]
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.comp_map]
  rw [← cancel_mono ((shiftFunctorAdd C a b).hom.app _), assoc, assoc, assoc, assoc,
    Iso.inv_hom_id_app]; erw [comp_id]
  rw [← (shiftFunctor C b).map_comp, ← (shiftFunctor C b).map_comp, ← h X]
  simp only [Functor.comp_obj, NatTrans.naturality, Functor.comp_map, Functor.id_obj]

end CommShift

variable (A) [F.CommShift A] [G.CommShift A]

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
    ext _
    simp [Functor.commShiftIso_comp_hom_app]
    refine (compat_counit_of_compat_unit adj a (F.commShiftIso a) (G.commShiftIso a) ?_ _).symm
    intro X
    have := h.comm' a
    apply_fun (fun x ↦ x.app X) at this
    simp [Functor.commShiftIso_comp_hom_app] at this
    exact this
  ⟩

end CommShift

variable {A}

@[reassoc]
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        G.map ((F.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (F.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.CommShift.comm_app adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (Y : D) :
    (adj.counit.app Y)⟦a⟧' =
      (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y)
        ≫ adj.counit.app (Y⟦a⟧) := by
  have eq := NatTrans.CommShift.comm_app adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.CommShift.commShiftIso_id_hom_app, comp_id] at eq
  rw [← eq, ← assoc (F.map ((G.commShiftIso a).inv.app _)), ← F.map_comp, Iso.inv_hom_id_app,
    F.map_id, id_comp, Iso.inv_hom_id_app_assoc]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]

namespace RightAdjointCommShift

variable (a b : A) (h : b + a = 0) [F.CommShift A]

/-- Auxiliary definition for `iso`. -/
noncomputable def iso' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
  (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

noncomputable def iso : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  iso' adj _ _ (neg_add_cancel a)

lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (G.map ((F.commShiftIso b).hom.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (G.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (G.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [Functor.comp_obj, iso, iso', shiftEquiv'_functor, shiftEquiv'_inverse,
    Equiv.toFun_as_coe, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app, comp_unit_app,
    Functor.id_obj, Equivalence.toAdjunction_unit, Functor.comp_map, comp_counit_app,
    Equivalence.toAdjunction_counit, Functor.map_comp, assoc]
  rfl

lemma iso_inv_app (Y : D) :
    (iso adj a).inv.app Y =
      adj.unit.app ((shiftFunctor C a).obj (G.obj Y)) ≫
          G.map ((shiftFunctorCompIsoId D b a h).inv.app
              (F.obj ((shiftFunctor C a).obj (G.obj Y)))) ≫
            G.map ((shiftFunctor D a).map ((shiftFunctor D b).map
                ((F.commShiftIso a).hom.app (G.obj Y)))) ≫
              G.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [eq_neg_of_add_eq_zero_left h, add_neg_cancel])).hom.app
                    (F.obj (G.obj Y)))) ≫
                G.map ((shiftFunctor D a).map (adj.counit.app Y)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [Functor.comp_obj, iso, iso', shiftEquiv'_functor, shiftEquiv'_inverse,
    Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv, conjugateEquiv_apply_app, comp_unit_app,
    Functor.id_obj, Equivalence.toAdjunction_unit, Functor.comp_map, comp_counit_app,
    Equivalence.toAdjunction_counit, Functor.map_comp, assoc]
  congr 2
  rw [← assoc, ← assoc]
  congr 1
  conv_rhs => rw [← G.map_comp, ← Functor.map_comp]
  conv_lhs => rw [← G.map_comp, ← Functor.map_comp]
  congr 2
  have this := F.commShiftIso_add' (add_neg_cancel a)
  apply_fun (fun x ↦ x.inv.app (G.obj Y)) at this
  rw [← cancel_epi ((shiftFunctorAdd' D a (-a) 0 (add_neg_cancel _)).inv.app _),
    ← cancel_mono (F.map ((shiftFunctorAdd' C a (-a) 0 (add_neg_cancel _)).hom.app _))] at this
  simp only [Functor.comp_obj, assoc, Functor.CommShift.isoAdd'_inv_app, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, comp_id] at this
  rw [← cancel_epi (((F.commShiftIso a).inv.app _)⟦-a⟧'), ← assoc, ← this, ← assoc, ← assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, id_comp, F.commShiftIso_zero]
  simp only [Functor.comp_obj, Functor.CommShift.isoZero_inv_app, assoc]
  rw [shiftEquiv'_counit, shiftFunctorCompIsoId]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp]
  slice_lhs 4 5 => rw [← F.map_comp, Iso.hom_inv_id_app, F.map_id]
  rw [id_comp, ← F.map_comp, Iso.inv_hom_id_app]
  erw [F.map_id]; rw [comp_id]
  rfl

lemma iso_compat_unit (a : A) : CommShift.compat_unit adj a (F.commShiftIso a) (iso adj a) := by
  intro X
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app (F.obj X)), assoc, assoc,
    Iso.hom_inv_id_app]
  dsimp
  rw [comp_id]
  simp [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp [homEquiv_counit]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    left_triangle_components, Functor.map_id, comp_id]

end RightAdjointCommShift

variable (A)

@[simps]
noncomputable def rightAdjointCommShift [F.CommShift A] : G.CommShift A where
  iso a := RightAdjointCommShift.iso adj a
  zero := by
    refine CommShift.compat_unit_unique_right adj 0 (F.commShiftIso 0)  _ _
      (RightAdjointCommShift.iso_compat_unit adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compat_unit_isoZero adj
  add a b := by
    refine CommShift.compat_unit_unique_right adj (a + b) (F.commShiftIso (a + b))  _ _
      (RightAdjointCommShift.iso_compat_unit adj (a + b)) ?_
    rw [F.commShiftIso_add]
    exact CommShift.compat_unit_isoAdd adj a b _ _ _ _
      (RightAdjointCommShift.iso_compat_unit adj a) (RightAdjointCommShift.iso_compat_unit adj b)

lemma commShift_of_leftAdjoint [F.CommShift A] :
    letI := adj.rightAdjointCommShift A
    adj.CommShift A := by
  letI := adj.rightAdjointCommShift A
  apply CommShift.mk'
  refine ⟨fun a => ?_⟩
  ext X
  dsimp
  simp only [Functor.CommShift.commShiftIso_id_hom_app, Functor.comp_obj,
    Functor.id_obj, id_comp, Functor.commShiftIso_comp_hom_app]
  exact RightAdjointCommShift.iso_compat_unit adj a X

end Adjunction

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] (E : C ≌ D)
  (A Z : Type*) [AddMonoid A] [AddGroup Z]
  [HasShift C A] [HasShift D A] [HasShift C Z] [HasShift D Z]

class CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop where
  commShift_unitIso_hom : NatTrans.CommShift E.unitIso.hom A := by infer_instance
  commShift_counitIso_hom : NatTrans.CommShift E.counitIso.hom A := by infer_instance

namespace CommShift

attribute [instance] commShift_unitIso_hom commShift_counitIso_hom

instance [h : E.functor.CommShift A] : E.symm.inverse.CommShift A := h
instance [h : E.inverse.CommShift A] : E.symm.functor.CommShift A := h

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk' [E.functor.CommShift A] [E.inverse.CommShift A]
    (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_counitIso_hom :=
    (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk'' [E.functor.CommShift A] [E.inverse.CommShift A]
    (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A where
  commShift_unitIso_hom := by
    have h' := NatTrans.CommShift.of_iso_inv E.counitIso A
    have : NatTrans.CommShift E.unitIso.symm.hom A :=
      (Adjunction.CommShift.mk' E.symm.toAdjunction A h').commShift_counit
    exact NatTrans.CommShift.of_iso_inv E.unitIso.symm A

instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.toAdjunction.CommShift A where
  commShift_unit := commShift_unitIso_hom
  commShift_counit := commShift_counitIso_hom

instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.symm.CommShift A := mk' _ _ (by
  dsimp only [Equivalence.symm, Iso.symm]
  infer_instance)

end CommShift

noncomputable def commShiftInverse [E.functor.CommShift Z] : E.inverse.CommShift Z :=
  E.toAdjunction.rightAdjointCommShift Z

lemma commShift_of_functor [E.functor.CommShift Z] :
    letI := E.commShiftInverse Z
    E.CommShift Z := by
  letI := E.commShiftInverse Z
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint Z).commShift_unit

noncomputable def commShiftFunctor [E.inverse.CommShift Z] : E.functor.CommShift Z :=
  E.symm.toAdjunction.rightAdjointCommShift Z

lemma commShift_of_inverse [E.inverse.CommShift Z] :
    letI := E.commShiftFunctor Z
    E.CommShift Z := by
  letI := E.commShiftFunctor Z
  apply CommShift.mk''
  have : NatTrans.CommShift E.counitIso.symm.hom Z :=
    (E.symm.toAdjunction.commShift_of_leftAdjoint Z).commShift_unit
  exact NatTrans.CommShift.of_iso_inv E.counitIso.symm Z

end Equivalence

end CategoryTheory
