import Mathlib.CategoryTheory.Shift.ShiftSequence

open CategoryTheory Category

namespace CategoryTheory

variable {C D A : Type _} [Category C] [Category D] [Category A]
  {L : C ⥤ D} {F : D ⥤ A} {G : C ⥤ A} (e : L ⋙ F ≅ G) (M : Type _)
  [AddMonoid M] [HasShift C M] [HasShift D M] [L.HasCommShift M]
  [G.ShiftSequence M] (F' : M → D ⥤ A) (e' : ∀ m, L ⋙ F' m ≅ G.shift m)
  (hL : Nonempty (Full ((whiskeringLeft C D A).obj L)) ∧ Faithful ((whiskeringLeft C D A).obj L))

namespace Functor

namespace ShiftSequence

noncomputable def induced_isoZero : F' 0 ≅ F :=
  letI := hL.1.some
  have := hL.2
  ((whiskeringLeft C D A).obj L).preimageIso (e' 0 ≪≫ G.isoShiftZero M ≪≫ e.symm)

lemma induced_isoZero_hom_app_obj' (X : C) :
    (induced_isoZero e M F' e' hL).hom.app (L.obj X) =
      (e' 0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X := by
  letI := hL.1.some
  have h : whiskerLeft L (induced_isoZero e M F' e' hL).hom = _ :=
    ((whiskeringLeft C D A).obj L).image_preimage _
  refine' (NatTrans.congr_app h X).trans (by simp)

variable (L G)

noncomputable def induced_shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor D n ⋙ F' a ≅ F' a' := by
  letI := hL.1.some
  have := hL.2
  exact ((whiskeringLeft C D A).obj L).preimageIso ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (L.commShiftIso n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (e' a) ≪≫
    G.shiftIso n a a' ha' ≪≫ (e' a').symm)

lemma induced_shiftIso_hom_app_obj' (n a a' : M) (ha' : n + a = a') (X : C) :
    (induced_shiftIso L G M F' e' hL n a a' ha').hom.app (L.obj X) =
      (F' a).map ((L.commShiftIso n).inv.app X) ≫
        (e' a).hom.app (X⟦n⟧) ≫ (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X := by
  letI := hL.1.some
  have h : whiskerLeft L (induced_shiftIso L G M F' e' hL n a a' ha').hom = _ :=
    ((whiskeringLeft C D A).obj L).image_preimage _
  exact (NatTrans.congr_app h X).trans (by simp)

attribute [irreducible] induced_isoZero induced_shiftIso

variable {L G}

noncomputable def induced : F.ShiftSequence M where
  sequence := F'
  isoZero := induced_isoZero e M F' e' hL
  shiftIso := induced_shiftIso L G M F' e' hL
  shiftIso_zero a := by
    have := hL.2
    ext1
    apply ((whiskeringLeft C D A).obj L).map_injective
    ext K
    dsimp
    simp only [induced_shiftIso_hom_app_obj', comp_obj, shiftIso_zero_hom_app, id_obj,
      NatTrans.naturality, comp_map, Iso.hom_inv_id_app_assoc,
      comp_id, ← Functor.map_comp, L.commShiftIso_zero, HasCommShift.iso_zero_inv_app, assoc,
      Iso.inv_hom_id_app, Functor.map_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    have := hL.2
    ext1
    apply ((whiskeringLeft C D A).obj L).map_injective
    ext K
    dsimp
    simp only [id_comp, induced_shiftIso_hom_app_obj',
      G.shiftIso_add_hom_app n m a a' a'' ha' ha'', L.commShiftIso_add,
      comp_obj, HasCommShift.iso_add_inv_app, (F' a).map_comp, assoc,
      ← (e' a).hom.naturality_assoc, comp_map]
    simp only [← NatTrans.naturality_assoc, induced_shiftIso_hom_app_obj',
      ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, comp_obj,
      Functor.map_id, id_comp]
    dsimp
    simp only [Functor.map_comp, assoc, Iso.inv_hom_id_app_assoc]

@[simp]
lemma induced_shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) :
    letI := (induced e M F' e' hL)
    (F.shiftIso n a a' ha').hom.app (L.obj X) =
      (F.shift a).map ((L.commShiftIso n).inv.app X) ≫ (e' a).hom.app (X⟦n⟧) ≫
        (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X := by
  apply induced_shiftIso_hom_app_obj'

end ShiftSequence

end Functor

end CategoryTheory
