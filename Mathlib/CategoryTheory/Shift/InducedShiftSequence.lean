/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.ShiftSequence

/-! # Induced shift sequences

When `G : C ⥤ A` is a functor from a category equipped with a shift by a
monoid `M`, we have defined in the file `CategoryTheory.Shift.ShiftSequence`
a type class `G.ShiftSequence M` which provides functors `G.shift a : C ⥤ A` for all `a : M`,
isomorphisms `shiftFunctor C n ⋙ G.shift a ≅ G.shift a'` when `n + a = a'`,
and isomorphisms `G.isoShift a : shiftFunctor C a ⋙ G ≅ G.shift a` for all `a`, all of
which satisfy good coherence properties. The idea is that it allows to use functors
`G.shift a` which may have better definitional properties than `shiftFunctor C a ⋙ G`.
The typical example shall be `[(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ]`
for any abelian category `C` (TODO).

Similarly as a shift on a category may induce a shift on a quotient or a localized
category (see the file `CategoryTheory.Shift.Induced`), this file shows that
under certain assumptions, there is an induced "shift sequence". The main application
will be the construction of a shift sequence for the homology functor on the
homotopy category of cochain complexes (TODO), and also on the derived category (TODO).

-/

open CategoryTheory Category Functor

namespace CategoryTheory

variable {C D A : Type*} [Category C] [Category D] [Category A]
  {L : C ⥤ D} {F : D ⥤ A} {G : C ⥤ A} (e : L ⋙ F ≅ G) (M : Type*)
  [AddMonoid M] [HasShift C M]
  [G.ShiftSequence M] (F' : M → D ⥤ A) (e' : ∀ m, L ⋙ F' m ≅ G.shift m)
  [((whiskeringLeft C D A).obj L).Full] [((whiskeringLeft C D A).obj L).Faithful]

namespace Functor

namespace ShiftSequence

namespace induced

/-- The `isoZero` field of the induced shift sequence. -/
noncomputable def isoZero : F' 0 ≅ F :=
  ((whiskeringLeft C D A).obj L).preimageIso (e' 0 ≪≫ G.isoShiftZero M ≪≫ e.symm)

lemma isoZero_hom_app_obj (X : C) :
    (isoZero e M F' e').hom.app (L.obj X) =
      (e' 0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X :=
  NatTrans.congr_app (((whiskeringLeft C D A).obj L).map_preimage _) X

variable (L G)
variable [HasShift D M] [L.CommShift M]

/-- The `shiftIso` field of the induced shift sequence. -/
noncomputable def shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor D n ⋙ F' a ≅ F' a' := by
  exact ((whiskeringLeft C D A).obj L).preimageIso ((Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (L.commShiftIso n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (e' a) ≪≫
    G.shiftIso n a a' ha' ≪≫ (e' a').symm)

lemma shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) :
    (shiftIso L G M F' e' n a a' ha').hom.app (L.obj X) =
      (F' a).map ((L.commShiftIso n).inv.app X) ≫
        (e' a).hom.app (X⟦n⟧) ≫ (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X :=
  (NatTrans.congr_app (((whiskeringLeft C D A).obj L).map_preimage _) X).trans (by simp)

attribute [irreducible] isoZero shiftIso

end induced

variable [HasShift D M] [L.CommShift M]

/-- Given an isomorphism of functors `e : L ⋙ F ≅ G` relating functors `L : C ⥤ D`,
`F : D ⥤ A` and `G : C ⥤ A`, an additive monoid `M`, a family of functors `F' : M → D ⥤ A`
equipped with isomorphisms `e' : ∀ m, L ⋙ F' m ≅ G.shift m`, this is the shift sequence
induced on `F` induced by a shift sequence for the functor `G`, provided that
the functor `(whiskeringLeft C D A).obj L` of precomposition by `L` is fully faithful. -/
noncomputable def induced : F.ShiftSequence M where
  sequence := F'
  isoZero := induced.isoZero e M F' e'
  shiftIso := induced.shiftIso L G M F' e'
  shiftIso_zero a := by
    ext1
    apply ((whiskeringLeft C D A).obj L).map_injective
    ext K
    dsimp
    simp only [induced.shiftIso_hom_app_obj, shiftIso_zero_hom_app, id_obj,
      NatTrans.naturality, comp_map, Iso.hom_inv_id_app_assoc,
      comp_id, ← Functor.map_comp, L.commShiftIso_zero, CommShift.isoZero_inv_app, assoc,
      Iso.inv_hom_id_app, Functor.map_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext1
    apply ((whiskeringLeft C D A).obj L).map_injective
    ext K
    dsimp
    simp only [id_comp, induced.shiftIso_hom_app_obj,
      G.shiftIso_add_hom_app n m a a' a'' ha' ha'', L.commShiftIso_add,
      comp_obj, CommShift.isoAdd_inv_app, (F' a).map_comp, assoc,
      ← (e' a).hom.naturality_assoc, comp_map]
    simp only [← NatTrans.naturality_assoc, induced.shiftIso_hom_app_obj,
      ← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app, comp_obj,
      Functor.map_id, id_comp]
    dsimp
    simp only [Functor.map_comp, assoc, Iso.inv_hom_id_app_assoc]

@[simp, reassoc]
lemma induced_isoShiftZero_hom_app_obj (X : C) :
    letI := (induced e M F' e')
    (F.isoShiftZero M).hom.app (L.obj X) =
      (e' 0).hom.app X ≫ (isoShiftZero G M).hom.app X ≫ e.inv.app X := by
  apply induced.isoZero_hom_app_obj

@[simp, reassoc]
lemma induced_shiftIso_hom_app_obj (n a a' : M) (ha' : n + a = a') (X : C) :
    letI := (induced e M F' e')
    (F.shiftIso n a a' ha').hom.app (L.obj X) =
      (F.shift a).map ((L.commShiftIso n).inv.app X) ≫ (e' a).hom.app (X⟦n⟧) ≫
        (G.shiftIso n a a' ha').hom.app X ≫ (e' a').inv.app X := by
  apply induced.shiftIso_hom_app_obj

@[reassoc]
lemma induced_shiftMap {n : M} {X Y : C} (f : X ⟶ Y⟦n⟧) (a a' : M) (h : n + a = a') :
    letI := induced e M F' e'
    F.shiftMap (L.map f ≫ (L.commShiftIso n).hom.app _) a a' h =
      (e' a).hom.app X ≫ G.shiftMap f a a' h ≫ (e' a').inv.app Y := by
  dsimp [shiftMap]
  rw [Functor.map_comp, induced_shiftIso_hom_app_obj, assoc, assoc]
  nth_rw 2 [← Functor.map_comp_assoc]
  simp only [comp_obj, Iso.hom_inv_id_app, map_id, id_comp]
  rw [← NatTrans.naturality_assoc]
  rfl

end ShiftSequence

end Functor

end CategoryTheory
