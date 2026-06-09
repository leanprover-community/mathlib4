/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Shift induced from a category to another

In this file, we introduce a sufficient condition on a functor
`F : C ⥤ D` so that a shift on `C` by a monoid `A` induces a shift on `D`.
More precisely, when the functor `(D ⥤ D) ⥤ C ⥤ D` given
by the precomposition with `F` is fully faithful, and that
all the shift functors on `C` can be lifted to functors `D ⥤ D`
(i.e. we have functors `s a : D ⥤ D` for all `a : A`, and isomorphisms
`F ⋙ s a ≅ shiftFunctor C a ⋙ F`), then these functors `s a` are
the shift functors of a term of type `HasShift D A`.

As this condition on the functor `F` is satisfied for quotient and localization
functors, the main construction `HasShift.induced` in this file shall be
used for both quotient and localized shifts.

-/

@[expose] public section

namespace CategoryTheory

open Functor

variable {C D : Type _} [Category* C] [Category* D]
  (F : C ⥤ D) {A : Type _} [AddMonoid A] [HasShift C A]
  (s : A → D ⥤ D) (i : ∀ a, F ⋙ s a ≅ shiftFunctor C a ⋙ F)
  [((whiskeringLeft C D D).obj F).Full] [((whiskeringLeft C D D).obj F).Faithful]

namespace HasShift

namespace Induced

/-- The `zero` field of the `ShiftMkCore` structure for the induced shift. -/
noncomputable def zero : s 0 ≅ 𝟭 D :=
  ((whiskeringLeft C D D).obj F).preimageIso ((i 0) ≪≫
    isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫ F.rightUnitor.symm)

/-- The `add` field of the `ShiftMkCore` structure for the induced shift. -/
noncomputable def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  ((whiskeringLeft C D D).obj F).preimageIso
    (i (a + b) ≪≫ isoWhiskerRight (shiftFunctorAdd C a b) F ≪≫
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (i b).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (i a).symm _ ≪≫ Functor.associator _ _ _)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma zero_hom_app_obj (X : C) :
    (zero F s i).hom.app (F.obj X) =
      (i 0).hom.app X ≫ F.map ((shiftFunctorZero C A).hom.app X) := by
  have h : whiskerLeft F (zero F s i).hom = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma zero_inv_app_obj (X : C) :
    (zero F s i).inv.app (F.obj X) =
      F.map ((shiftFunctorZero C A).inv.app X) ≫ (i 0).inv.app X := by
  have h : whiskerLeft F (zero F s i).inv = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma add_hom_app_obj (a b : A) (X : C) :
    (add F s i a b).hom.app (F.obj X) =
      (i (a + b)).hom.app X ≫ F.map ((shiftFunctorAdd C a b).hom.app X) ≫
        (i b).inv.app ((shiftFunctor C a).obj X) ≫ (s b).map ((i a).inv.app X) := by
  have h : whiskerLeft F (add F s i a b).hom = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma add_inv_app_obj (a b : A) (X : C) :
    (add F s i a b).inv.app (F.obj X) =
      (s b).map ((i a).hom.app X) ≫ (i b).hom.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) ≫ (i (a + b)).inv.app X := by
  have h : whiskerLeft F (add F s i a b).inv = _ :=
    ((whiskeringLeft C D D).obj F).map_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

end Induced

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `F : C ⥤ D` is a functor satisfying suitable technical assumptions,
this is the induced term of type `HasShift D A` deduced from `[HasShift C A]`. -/
@[implicit_reducible]
noncomputable def induced : HasShift D A :=
  hasShiftMk D A
    { F := s
      zero := Induced.zero F s i
      add := Induced.add F s i
      zero_add_hom_app := fun n => by
        suffices (Induced.add F s i 0 n).hom =
          eqToHom (by rw [zero_add]; rfl) ≫ whiskerRight (Induced.zero F s i).inv (s n) by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        have eq := dcongr_arg (fun a => (i a).hom.app X) (zero_add n)
        dsimp
        simp only [Induced.add_hom_app_obj, eq, shiftFunctorAdd_zero_add_hom_app,
          Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, eqToHom_app, Induced.zero_inv_app_obj]
        erw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]
        rfl
      add_zero_hom_app := fun n => by
        suffices (Induced.add F s i n 0).hom =
            eqToHom (by rw [add_zero]; rfl) ≫ whiskerLeft (s n) (Induced.zero F s i).inv by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        dsimp
        erw [Induced.add_hom_app_obj, dcongr_arg (fun a => (i a).hom.app X) (add_zero n),
          ← cancel_mono ((s 0).map ((i n).hom.app X)), Category.assoc,
          Category.assoc, Category.assoc, Category.assoc, Category.assoc,
          Category.assoc, ← (s 0).map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id,
          ← NatTrans.naturality, Induced.zero_inv_app_obj,
          shiftFunctorAdd_add_zero_hom_app]
        simp [eqToHom_map, eqToHom_app]
      assoc_hom_app := fun m₁ m₂ m₃ => by
        suffices (Induced.add F s i (m₁ + m₂) m₃).hom ≫
            whiskerRight (Induced.add F s i m₁ m₂).hom (s m₃) =
            eqToHom (by rw [add_assoc]) ≫ (Induced.add F s i m₁ (m₂ + m₃)).hom ≫
              whiskerLeft (s m₁) (Induced.add F s i m₂ m₃).hom by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        dsimp
        have eq := F.congr_map (shiftFunctorAdd'_assoc_hom_app
          m₁ m₂ m₃ _ _ (m₁ + m₂ + m₃) rfl rfl rfl X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at eq
        simp only [Functor.comp_obj, Functor.map_comp, shiftFunctorAdd',
          Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
          Category.assoc] at eq
        rw [← cancel_mono ((s m₃).map ((s m₂).map ((i m₁).hom.app X)))]
        simp only [Induced.add_hom_app_obj, Category.assoc, Functor.map_comp]
        slice_lhs 4 5 =>
          erw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
        erw [Category.id_comp]
        slice_lhs 6 7 =>
          erw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
            (s m₂).map_id, (s m₃).map_id]
        erw [Category.comp_id, ← NatTrans.naturality_assoc, reassoc_of% eq,
          dcongr_arg (fun a => (i a).hom.app X) (add_assoc m₁ m₂ m₃).symm]
        simp only [Functor.comp_obj, eqToHom_map, eqToHom_app, NatTrans.naturality_assoc,
          Induced.add_hom_app_obj, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app_assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id] }

end HasShift

lemma shiftFunctor_of_induced (a : A) :
    letI := HasShift.induced F A s i
    shiftFunctor D a = s a :=
  rfl

variable (A)

@[simp]
lemma shiftFunctorZero_hom_app_obj_of_induced (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorZero D A).hom.app (F.obj X) =
      (i 0).hom.app X ≫ F.map ((shiftFunctorZero C A).hom.app X) := by
  simp only [ShiftMkCore.shiftFunctorZero_eq, HasShift.Induced.zero_hom_app_obj]

@[simp]
lemma shiftFunctorZero_inv_app_obj_of_induced (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorZero D A).inv.app (F.obj X) =
      F.map ((shiftFunctorZero C A).inv.app X) ≫ (i 0).inv.app X := by
  simp only [ShiftMkCore.shiftFunctorZero_eq, HasShift.Induced.zero_inv_app_obj]

variable {A}

@[simp]
lemma shiftFunctorAdd_hom_app_obj_of_induced (a b : A) (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorAdd D a b).hom.app (F.obj X) =
      (i (a + b)).hom.app X ≫
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫
        (i b).inv.app ((shiftFunctor C a).obj X) ≫
        (s b).map ((i a).inv.app X) := by
  simp only [ShiftMkCore.shiftFunctorAdd_eq, HasShift.Induced.add_hom_app_obj]

@[simp]
lemma shiftFunctorAdd_inv_app_obj_of_induced (a b : A) (X : C) :
    letI := HasShift.induced F A s i
    (shiftFunctorAdd D a b).inv.app (F.obj X) =
      (s b).map ((i a).hom.app X) ≫
      (i b).hom.app ((shiftFunctor C a).obj X) ≫
      F.map ((shiftFunctorAdd C a b).inv.app X) ≫
      (i (a + b)).inv.app X := by
  simp only [ShiftMkCore.shiftFunctorAdd_eq, HasShift.Induced.add_inv_app_obj]

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When the target category of a functor `F : C ⥤ D` is equipped with
the induced shift, this is the compatibility of `F` with the shifts on
the categories `C` and `D`. -/
@[implicit_reducible]
noncomputable def Functor.CommShift.ofInduced :
    letI := HasShift.induced F A s i
    F.CommShift A := by
  letI := HasShift.induced F A s i
  exact
    { commShiftIso := fun a => (i a).symm
      commShiftIso_zero := by
        ext X
        dsimp
        simp only [isoZero_hom_app, shiftFunctorZero_inv_app_obj_of_induced,
          ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
      commShiftIso_add := fun a b => by
        ext X
        dsimp
        simp only [isoAdd_hom_app, Iso.symm_hom, shiftFunctorAdd_inv_app_obj_of_induced,
          shiftFunctor_of_induced]
        rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
        dsimp
        rw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
          ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp] }

lemma Functor.commShiftIso_eq_ofInduced (a : A) :
    letI := HasShift.induced F A s i
    letI := Functor.CommShift.ofInduced F A s i
    F.commShiftIso a = (i a).symm := rfl

end CategoryTheory
