import Mathlib.CategoryTheory.Shift.CommShift

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]
  (F : C ⥤ D) {A : Type _} [AddMonoid A] [HasShift C A]
  (s : A → D ⥤ D) (i : ∀ a, F ⋙ s a ≅ shiftFunctor C a ⋙ F)
  (hF : Nonempty (Full ((whiskeringLeft C D D).obj F)) ∧ Faithful ((whiskeringLeft C D D).obj F))

namespace HasShift

noncomputable def induced_zero : s 0 ≅ 𝟭 D :=
  letI := hF.1.some
  letI := hF.2
  ((whiskeringLeft C D D).obj F).preimageIso ((i 0) ≪≫
    isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫ F.rightUnitor.symm)

noncomputable def induced_add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  letI := hF.1.some
  letI := hF.2
  ((whiskeringLeft C D D).obj F).preimageIso
    (i (a + b) ≪≫ isoWhiskerRight (shiftFunctorAdd C a b) F ≪≫
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (i b).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (i a).symm _ ≪≫ Functor.associator _ _ _)

@[simp]
lemma induced_zero_hom_app_obj (X : C) :
  (induced_zero F s i hF).hom.app (F.obj X) =
    (i 0).hom.app X ≫ F.map ((shiftFunctorZero C A).hom.app X) := by
  letI := hF.1.some
  letI := hF.2
  have h : whiskerLeft F (induced_zero F s i hF).hom = _ :=
    ((whiskeringLeft C D D).obj F).image_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

@[simp]
lemma induced_zero_inv_app_obj (X : C) :
  (induced_zero F s i hF).inv.app (F.obj X) =
    F.map ((shiftFunctorZero C A).inv.app X) ≫ (i 0).inv.app X := by
  letI := hF.1.some
  letI := hF.2
  have h : whiskerLeft F (induced_zero F s i hF).inv = _ :=
    ((whiskeringLeft C D D).obj F).image_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

@[simp]
lemma induced_add_hom_app_obj (a b : A) (X : C) :
  (induced_add F s i hF a b).hom.app (F.obj X) =
    (i (a + b)).hom.app X ≫
      F.map ((shiftFunctorAdd C a b).hom.app X) ≫
      (i b).inv.app ((shiftFunctor C a).obj X) ≫
      (s b).map ((i a).inv.app X) := by
  letI := hF.1.some
  letI := hF.2
  have h : whiskerLeft F (induced_add F s i hF a b).hom = _ :=
    ((whiskeringLeft C D D).obj F).image_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

@[simp]
lemma induced_add_inv_app_obj (a b : A) (X : C) :
  (induced_add F s i hF a b).inv.app (F.obj X) =
    (s b).map ((i a).hom.app X) ≫
    (i b).hom.app ((shiftFunctor C a).obj X) ≫
    F.map ((shiftFunctorAdd C a b).inv.app X) ≫
    (i (a + b)).inv.app X := by
  letI := hF.1.some
  letI := hF.2
  have h : whiskerLeft F (induced_add F s i hF a b).inv = _ :=
    ((whiskeringLeft C D D).obj F).image_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

variable (A)

noncomputable def induced : HasShift D A :=
  hasShiftMk D A
    { F := s
      zero := induced_zero F s i hF
      add := induced_add F s i hF
      zero_add_hom_app := fun n => by
        letI := hF.2
        suffices (induced_add F s i hF 0 n).hom =
          eqToHom (by rw [zero_add]; rfl) ≫ whiskerRight (induced_zero F s i hF).inv (s n) by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        have eq := dcongr_arg (fun a => (i a).hom.app X) (zero_add n)
        dsimp
        simp only [induced_add_hom_app_obj, eq, shiftFunctorAdd_zero_add_hom_app,
          Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
          eqToHom_refl, Category.id_comp, eqToHom_app, induced_zero_inv_app_obj]
        erw [← NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]
        rfl
      add_zero_hom_app := fun n => by
        letI := hF.2
        suffices (induced_add F s i hF n 0).hom =
            eqToHom (by rw [add_zero]; rfl) ≫ whiskerLeft (s n) (induced_zero F s i hF).inv  by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        dsimp
        erw [induced_add_hom_app_obj, dcongr_arg (fun a => (i a).hom.app X) (add_zero n),
          ← cancel_mono ((s 0).map ((i n).hom.app X)), Category.assoc,
          Category.assoc, Category.assoc, Category.assoc, Category.assoc,
          Category.assoc, ← (s 0).map_comp, Iso.inv_hom_id_app, Functor.map_id, Category.comp_id,
          ← NatTrans.naturality, induced_zero_inv_app_obj,
          shiftFunctorAdd_add_zero_hom_app]
        simp [eqToHom_map, eqToHom_app]
      assoc_hom_app := fun m₁ m₂ m₃ => by
        letI := hF.2
        suffices (induced_add F s i hF (m₁ + m₂) m₃).hom ≫
            whiskerRight (induced_add F s i hF m₁ m₂).hom (s m₃) =
            eqToHom (by rw [add_assoc]) ≫ (induced_add F s i hF m₁ (m₂ + m₃)).hom ≫
              whiskerLeft (s m₁) (induced_add F s i hF m₂ m₃).hom by
          intro X
          simpa using NatTrans.congr_app this X
        apply ((whiskeringLeft C D D).obj F).map_injective
        ext X
        dsimp
        have eq := F.congr_map (shiftFunctorAdd'_assoc_hom_app
          m₁ m₂ m₃ _ _ (m₁+m₂+m₃) rfl rfl rfl X)
        simp only [shiftFunctorAdd'_eq_shiftFunctorAdd] at eq
        simp only [Functor.comp_obj, Functor.map_comp, shiftFunctorAdd',
          Iso.trans_hom, eqToIso.hom, NatTrans.comp_app, eqToHom_app,
          Category.assoc] at eq
        rw [← cancel_mono ((s m₃).map ((s m₂).map ((i m₁).hom.app X)))]
        simp only [induced_add_hom_app_obj, Category.assoc, Functor.map_comp]
        slice_lhs 4 5 =>
          erw [← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
        erw [Category.id_comp]
        slice_lhs 6 7 =>
          erw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
            (s m₂).map_id, (s m₃).map_id]
        erw [Category.comp_id, ←NatTrans.naturality_assoc, reassoc_of% eq,
          dcongr_arg (fun a => (i a).hom.app X) (add_assoc m₁ m₂ m₃).symm]
        simp only [Functor.comp_obj, eqToHom_map, eqToHom_app, NatTrans.naturality_assoc,
          induced_add_hom_app_obj, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app_assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
          ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id] }

end HasShift

@[simp]
lemma shiftFunctor_of_induced (a : A) :
  letI := HasShift.induced F A s i hF
  shiftFunctor D a = s a := by
  rfl

variable (A)

@[simp]
lemma shiftFunctorZero_hom_app_obj_of_induced (X : C) :
  letI := HasShift.induced F A s i hF
  (shiftFunctorZero D A).hom.app (F.obj X) =
    (i 0).hom.app X ≫ F.map ((shiftFunctorZero C A).hom.app X) := by
  letI := HasShift.induced F A s i
  simp only [ShiftMkCore.shiftFunctorZero_eq, HasShift.induced_zero_hom_app_obj]

@[simp]
lemma shiftFunctorZero_inv_app_obj_of_induced (X : C) :
  letI := HasShift.induced F A s i hF
  (shiftFunctorZero D A).inv.app (F.obj X) =
    F.map ((shiftFunctorZero C A).inv.app X) ≫ (i 0).inv.app X := by
  letI := HasShift.induced F A s i
  simp only [ShiftMkCore.shiftFunctorZero_eq, HasShift.induced_zero_inv_app_obj]

variable {A}

@[simp]
lemma shiftFunctorAdd_hom_app_obj_of_induced (a b : A) (X : C) :
  letI := HasShift.induced F A s i hF
  (shiftFunctorAdd D a b).hom.app (F.obj X) =
    (i (a + b)).hom.app X ≫
      F.map ((shiftFunctorAdd C a b).hom.app X) ≫
      (i b).inv.app ((shiftFunctor C a).obj X) ≫
      (s b).map ((i a).inv.app X) := by
  letI := HasShift.induced F A s i
  simp only [ShiftMkCore.shiftFunctorAdd_eq, HasShift.induced_add_hom_app_obj]

@[simp]
lemma induced_add_inv_app_obj (a b : A) (X : C) :
    letI := HasShift.induced F A s i hF
    (shiftFunctorAdd D a b).inv.app (F.obj X) =
      (s b).map ((i a).hom.app X) ≫
      (i b).hom.app ((shiftFunctor C a).obj X) ≫
      F.map ((shiftFunctorAdd C a b).inv.app X) ≫
      (i (a + b)).inv.app X := by
  letI := HasShift.induced F A s i
  simp only [ShiftMkCore.shiftFunctorAdd_eq, HasShift.induced_add_inv_app_obj]

variable (A)
def Functor.CommShift.of_induced :
    letI := HasShift.induced F A s i hF
    F.CommShift A := by
  letI := HasShift.induced F A s i hF
  exact
  { iso := fun a => (i a).symm
    zero := by
      ext X
      dsimp
      simp only [isoZero_hom_app, shiftFunctorZero_inv_app_obj_of_induced,
        ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
    add := fun a b => by
      ext X
      dsimp
      simp only [isoAdd_hom_app, Iso.symm_hom, induced_add_inv_app_obj,
        shiftFunctor_of_induced]
      erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
        Category.id_comp, Iso.inv_hom_id_app_assoc, ←F.map_comp_assoc, Iso.hom_inv_id_app,
        F.map_id, Category.id_comp] }

lemma Functor.commShiftIso_eq_of_induced (a : A) :
    letI := HasShift.induced F A s i hF
    letI := Functor.CommShift.of_induced F A s i hF
    F.commShiftIso a = (i a).symm := rfl

end CategoryTheory
