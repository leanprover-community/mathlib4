import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

namespace Triangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

namespace TStructure

variable (X : C) {n a a' b b' : ℤ} (h : n + a = a') (h' : n + b = b')

namespace ShiftTruncLE

noncomputable def hom : ((t.truncLE a').obj X)⟦n⟧ ⟶ (t.truncLE a).obj (X⟦n⟧) := by
  have := t.isLE_shift ((t.truncLE a').obj X) a' n a h
  exact t.liftTruncLE (((t.truncLEι a').app X)⟦n⟧') a

@[reassoc (attr := simp)]
lemma hom_ι : hom t X h ≫ (t.truncLEι _).app _ = ((t.truncLEι a').app X)⟦n⟧' := by
  have := t.isLE_shift ((t.truncLE a').obj X) a' n a h
  apply liftTruncLE_ι

noncomputable def inv' : ((t.truncLE a).obj (X⟦n⟧))⟦-n⟧ ⟶ (t.truncLE a').obj X := by
  have := t.isLE_shift ((t.truncLE a).obj (X⟦n⟧)) a (-n) a' (by linarith)
  apply t.liftTruncLE
  exact (shiftEquiv C n).inverse.map ((t.truncLEι a).app (X⟦n⟧)) ≫ (shiftEquiv C n).unitIso.inv.app X

@[reassoc (attr := simp)]
lemma inv'_ι :
    inv' t X h ≫ (t.truncLEι a').app X =
      ((t.truncLEι a).app (X⟦n⟧))⟦-n⟧' ≫ (shiftEquiv C n).unitIso.inv.app X := by
  have := t.isLE_shift ((t.truncLE a).obj (X⟦n⟧)) a (-n) a' (by linarith)
  apply liftTruncLE_ι

noncomputable def inv :
    (t.truncLE a).obj (X⟦n⟧) ⟶ ((t.truncLE a').obj X)⟦n⟧ :=
  (shiftFunctorCompIsoId C (-n) n (neg_add_self n)).inv.app ((t.truncLE a).obj (X⟦n⟧)) ≫ (inv' t X h)⟦n⟧'

@[reassoc (attr := simp)]
lemma inv_ι : inv t X h ≫ ((t.truncLEι a').app X)⟦n⟧' = (t.truncLEι a).app (X⟦n⟧) := by
  dsimp only [inv]
  rw [assoc, ← Functor.map_comp, inv'_ι]
  dsimp
  rw [Functor.map_comp]
  erw [← NatTrans.naturality_assoc]
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj,
    shift_shiftFunctorCompIsoId_add_neg_self_hom_app, Iso.inv_hom_id_app, comp_id]

@[reassoc (attr := simp)]
lemma shift_inv :
    (inv t X h)⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).hom.app _ ≫
      (t.truncLEι a').app X =
    ((t.truncLEι a).app (X⟦n⟧))⟦-n⟧' ≫
      (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).hom.app _ := by
  dsimp
  erw [← NatTrans.naturality]
  dsimp
  rw [← Functor.map_comp_assoc, inv_ι]

@[simps]
noncomputable def iso : ((t.truncLE a').obj X)⟦n⟧ ≅ (t.truncLE a).obj (X⟦n⟧) where
  hom := hom t X h
  inv := inv t X h
  hom_inv_id := by
    apply ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).symm.injective
    dsimp
    have := t.isLE_shift ((t.truncLE a').obj X) a' n a h
    have := t.isLE_shift ((((t.truncLE a').obj X)⟦n⟧)) a (-n) a' (by linarith)
    apply to_truncLE_obj_ext
    dsimp
    simp only [Equivalence.symm, shiftEquiv'_inverse, shiftEquiv'_functor, shiftEquiv'_counitIso,
      shiftEquiv'_unitIso, Adjunction.homEquiv_counit, Functor.id_obj, Functor.map_comp,
      Equivalence.toAdjunction_counit, Equivalence.Equivalence_mk'_counit, Iso.symm_symm_eq, assoc,
      shift_inv, Functor.map_id, id_comp]
    rw [← Functor.map_comp_assoc, hom_ι]
    exact (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).hom.naturality ((t.truncLEι a').app X)
  inv_hom_id := by
    apply to_truncLE_obj_ext
    simp

end ShiftTruncLE

namespace ShiftTruncGE

noncomputable def hom : (t.truncGE a).obj (X⟦n⟧) ⟶ ((t.truncGE a').obj X)⟦n⟧ := by
  have := t.isGE_shift ((t.truncGE a').obj X) a' n a h
  apply t.descTruncGE (((t.truncGEπ a').app X)⟦n⟧') a

@[reassoc (attr := simp)]
lemma π_hom : (t.truncGEπ a).app (X⟦n⟧) ≫ hom t X h = ((t.truncGEπ a').app X)⟦n⟧' := by
  have := t.isGE_shift ((t.truncGE a').obj X) a' n a h
  apply π_descTruncGE

noncomputable def inv' : (t.truncGE a').obj X ⟶ ((t.truncGE a).obj (X⟦n⟧))⟦-n⟧  := by
  have := t.isGE_shift ((t.truncGE a).obj (X⟦n⟧)) a (-n) a' (by linarith)
  apply t.descTruncGE
  exact (shiftEquiv C n).unitIso.hom.app X ≫ ((t.truncGEπ a).app (X⟦n⟧))⟦-n⟧'

@[reassoc (attr := simp)]
lemma π_inv' :
    (t.truncGEπ a').app X ≫ inv' t X h =
      (shiftEquiv C n).unitIso.hom.app X ≫ ((t.truncGEπ a).app (X⟦n⟧))⟦-n⟧' := by
  have := t.isGE_shift ((t.truncGE a).obj (X⟦n⟧)) a (-n) a' (by linarith)
  apply t.π_descTruncGE

noncomputable def inv :
    ((t.truncGE a').obj X)⟦n⟧ ⟶ (t.truncGE a).obj (X⟦n⟧) :=
  (inv' t X h)⟦n⟧' ≫ (shiftFunctorCompIsoId C (-n) n (neg_add_self n)).hom.app
    ((t.truncGE a).obj (X⟦n⟧))

@[reassoc (attr := simp)]
lemma π_inv :
    (((t.truncGEπ a')).app X)⟦n⟧' ≫ inv t X h = (t.truncGEπ a).app (X⟦n⟧) := by
  dsimp only [inv]
  rw [← Functor.map_comp_assoc, π_inv']
  dsimp
  rw [Functor.map_comp, assoc]
  erw [(shiftFunctorCompIsoId C (-n) n (neg_add_self n)).hom.naturality]
  dsimp
  rw [shift_shiftFunctorCompIsoId_add_neg_self_inv_app, Iso.inv_hom_id_app_assoc]

@[reassoc (attr := simp)]
lemma shift_inv :
    (t.truncGEπ a').app X ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.app ((t.truncGE a').obj X) ≫
      (inv t X h)⟦-n⟧' =
        (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.app _ ≫
          ((t.truncGEπ a).app (X⟦n⟧))⟦-n⟧' := by
  dsimp
  erw [(shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.naturality_assoc]
  dsimp
  erw [← Functor.map_comp, π_inv]

@[simps]
noncomputable def iso : (t.truncGE a).obj (X⟦n⟧) ≅ ((t.truncGE a').obj X)⟦n⟧ where
  hom := hom t X h
  inv := inv t X h
  hom_inv_id := by
    apply from_truncGE_obj_ext
    simp
  inv_hom_id := by
    apply ((shiftEquiv C n).toAdjunction.homEquiv _ _).injective
    dsimp
    have := t.isGE_shift ((t.truncGE a').obj X) a' n a h
    have := t.isGE_shift (((t.truncGE a').obj X)⟦n⟧) a (-n) a' (by linarith)
    apply from_truncGE_obj_ext
    dsimp
    simp only [Adjunction.homEquiv_unit, Functor.id_obj, Functor.comp_obj,
      Equivalence.toAdjunction_unit, Functor.map_comp, Functor.map_id, comp_id]
    erw [shift_inv_assoc t X h]
    rw [← Functor.map_comp, π_hom]
    exact ((shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.naturality _).symm

end ShiftTruncGE

variable (n a a' b b')

noncomputable def shiftTruncLE :
    t.truncLE a' ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ t.truncLE a :=
  NatIso.ofComponents (fun X => ShiftTruncLE.iso t X h) (fun {X Y} f => by
    dsimp
    have := t.isLE_shift ((t.truncLE a').obj X) a' n a h
    apply to_truncLE_obj_ext
    simp only [Functor.id_obj, assoc, ShiftTruncLE.hom_ι, NatTrans.naturality, Functor.id_map,
      ShiftTruncLE.hom_ι_assoc, ← Functor.map_comp])

@[reassoc (attr := simp)]
lemma shiftTruncLE_hom_app_ι :
    (t.shiftTruncLE n a a' h).hom.app X ≫ (t.truncLEι a).app (X⟦n⟧) =
      ((t.truncLEι a').app X)⟦n⟧' := by
  simp [shiftTruncLE]

noncomputable def shiftTruncGE :
    t.truncGE a' ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ t.truncGE a :=
  Iso.symm (NatIso.ofComponents (fun X => ShiftTruncGE.iso t X h) (fun {X Y} f => by
    dsimp
    have := t.isGE_shift ((t.truncGE a').obj Y) a' n a h
    apply from_truncGE_obj_ext
    dsimp
    rw [ShiftTruncGE.π_hom_assoc, ← NatTrans.naturality_assoc, ShiftTruncGE.π_hom]
    dsimp
    rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.naturality]
    rfl))

@[reassoc (attr := simp)]
lemma π_shiftTruncGE_inv_app :
    (t.truncGEπ a).app (X⟦n⟧) ≫ (t.shiftTruncGE n a a' h).inv.app X =
      ((t.truncGEπ a').app X)⟦n⟧' := by
  simp [shiftTruncGE]

noncomputable def shiftTruncGELE :
    t.truncGELE a' b' ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ t.truncGELE a b :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (t.truncLE b') (t.shiftTruncGE n a a' h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (t.shiftTruncLE n b b' h') (t.truncGE a) ≪≫ Functor.associator _ _ _

end TStructure

end Triangulated

end CategoryTheory
