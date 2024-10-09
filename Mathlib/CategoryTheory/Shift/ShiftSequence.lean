/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Sequences of functors from a category equipped with a shift

Let `F : C ⥤ A` be a functor from a category `C` that is equipped with a
shift by an additive monoid `M`. In this file, we define a typeclass
`F.ShiftSequence M` which includes the data of a sequence of functors
`F.shift a : C ⥤ A` for all `a : A`. For each `a : A`, we have
an isomorphism `F.isoShift a : shiftFunctor C a ⋙ F ≅ F.shift a` which
satisfies some coherence relations. This allows to state results
(e.g. the long exact sequence of an homology functor (TODO)) using
functors `F.shift a` rather than `shiftFunctor C a ⋙ F`. The reason
for this design is that we can often choose functors `F.shift a` that
have better definitional properties than `shiftFunctor C a ⋙ F`.
For example, if `C` is the derived category (TODO) of an abelian
category `A` and `F` is the homology functor in degree `0`, then
for any `n : ℤ`, we may choose `F.shift n` to be the homology functor
in degree `n`.

-/

open CategoryTheory Category ZeroObject Limits

variable {C A : Type*} [Category C] [Category A] (F : C ⥤ A)
  (M : Type*) [AddMonoid M] [HasShift C M]
  {G : Type*} [AddGroup G] [HasShift C G]

namespace CategoryTheory

namespace Functor

/-- A shift sequence for a functor `F : C ⥤ A` when `C` is equipped with a shift
by a monoid `M` involves a sequence of functor `sequence n : C ⥤ A` for all `n : M`
which behave like `shiftFunctor C n ⋙ F`. -/
class ShiftSequence where
  /-- a sequence of functors -/
  sequence : M → C ⥤ A
  /-- `sequence 0` identifies to the given functor -/
  isoZero : sequence 0 ≅ F
  /-- compatibility isomorphism with the shift -/
  shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ sequence a ≅ sequence a'
  shiftIso_zero (a : M) : shiftIso 0 a a (zero_add a) =
    isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
  shiftIso_add : ∀ (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''),
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''

/-- The tautological shift sequence on a functor. -/
noncomputable def ShiftSequence.tautological : ShiftSequence F M where
  sequence n := shiftFunctor C n ⋙ F
  isoZero := isoWhiskerRight (shiftFunctorZero C M) F ≪≫ F.rightUnitor
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorAdd' C n a a' ha').symm _
  shiftIso_zero a := by
    dsimp
    rw [shiftFunctorAdd'_zero_add]
    aesop_cat
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [id_comp, ← Functor.map_comp]
    congr
    simpa only [← cancel_epi ((shiftFunctor C a).map ((shiftFunctorAdd C m n).hom.app X)),
      shiftFunctorAdd'_eq_shiftFunctorAdd, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, id_comp] using shiftFunctorAdd'_assoc_inv_app m n a (m+n) a' a'' rfl ha'
        (by rw [← ha'', ← ha', add_assoc]) X

section

variable {M}
variable [F.ShiftSequence M]

/-- The shifted functors given by the shift sequence. -/
def shift (n : M) : C ⥤ A := ShiftSequence.sequence F n

/-- Compatibility isomorphism `shiftFunctor C n ⋙ F.shift a ≅ F.shift a'` when `n + a = a'`. -/
def shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor C n ⋙ F.shift a ≅ F.shift a' :=
  ShiftSequence.shiftIso n a a' ha'

@[reassoc (attr := simp 1100)]
lemma shiftIso_hom_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a).map (f⟦n⟧') ≫ (shiftIso F n a a' ha').hom.app Y =
      (shiftIso F n a a' ha').hom.app X ≫ (shift F a').map f :=
  (F.shiftIso n a a' ha').hom.naturality f

@[reassoc (attr := simp 1100)]
lemma shiftIso_inv_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a').map f ≫ (shiftIso F n a a' ha').inv.app Y =
      (shiftIso F n a a' ha').inv.app X ≫ (shift F a).map (f⟦n⟧') :=
  (F.shiftIso n a a' ha').inv.naturality f

variable (M)

/-- The canonical isomorphism `F.shift 0 ≅ F`. -/
def isoShiftZero : F.shift (0 : M) ≅ F := ShiftSequence.isoZero

variable {M}

/-- The canonical isomorphism `shiftFunctor C n ⋙ F ≅ F.shift n`. -/
def isoShift (n : M) : shiftFunctor C n ⋙ F ≅ F.shift n :=
  isoWhiskerLeft _ (F.isoShiftZero M).symm ≪≫ F.shiftIso _ _ _ (add_zero n)

@[reassoc]
lemma isoShift_hom_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
    F.map (f⟦n⟧') ≫ (F.isoShift n).hom.app Y =
      (F.isoShift n).hom.app X ≫ (F.shift n).map f :=
  (F.isoShift n).hom.naturality f

attribute [simp] isoShift_hom_naturality

@[reassoc]
lemma isoShift_inv_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
    (F.shift n).map f ≫ (F.isoShift n).inv.app Y =
      (F.isoShift n).inv.app X ≫ F.map (f⟦n⟧') :=
  (F.isoShift n).inv.naturality f

lemma shiftIso_zero (a : M) :
    F.shiftIso 0 a a (zero_add a) =
      isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _ :=
  ShiftSequence.shiftIso_zero a

@[simp]
lemma shiftIso_zero_hom_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X =
      (shift F a).map ((shiftFunctorZero C M).hom.app X) := by
  simp [F.shiftIso_zero a]

@[simp]
lemma shiftIso_zero_inv_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X =
      (shift F a).map ((shiftFunctorZero C M).inv.app X) := by
  simp [F.shiftIso_zero a]

lemma shiftIso_add (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' :=
  ShiftSequence.shiftIso_add _ _ _ _ _ _ _

lemma shiftIso_add_hom_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shift F a).map ((shiftFunctorAdd C m n).hom.app X) ≫
        (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
          (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add_inv_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
        (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
          (shift F a).map ((shiftFunctorAdd C m n).inv.app X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add' (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerRight (shiftFunctorAdd' C m n _ hnm) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftIso_add]

lemma shiftIso_add'_hom_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shift F a).map ((shiftFunctorAdd' C m n mn hnm).hom.app X) ≫
        (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
          (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

lemma shiftIso_add'_inv_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
        (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
        (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[reassoc]
lemma shiftIso_hom_app_comp (n m mn : M) (hnm : m + n = mn)
    (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
      (shiftIso F m a' a'' ha'').hom.app X =
        (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) ≫
          (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X := by
  rw [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'', ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, id_comp]

/-- The morphism `(F.shift a).obj X ⟶ (F.shift a').obj Y` induced by a morphism
`f : X ⟶ Y⟦n⟧` when `n + a = a'`. -/
def shiftMap {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a') :
    (F.shift a).obj X ⟶ (F.shift a').obj Y :=
  (F.shift a).map f ≫ (F.shiftIso _ _ _ ha').hom.app Y

@[reassoc]
lemma shiftMap_comp {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g⟦n⟧') a a' ha' = F.shiftMap f a a' ha' ≫ (F.shift a').map g := by
  simp [shiftMap]

@[reassoc]
lemma shiftMap_comp' {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g) a a' ha' = (F.shift a).map f ≫ F.shiftMap g a a' ha' := by
  simp [shiftMap]

/--
When `f : X ⟶ Y⟦m⟧`, `m + n = mn`, `n + a = a'` and `ha'' : m + a' = a''`, this lemma
relates the two morphisms `F.shiftMap f a' a'' ha''` and `(F.shift a).map (f⟦n⟧')`. Indeed,
via canonical isomorphisms, they both identity to morphisms
`(F.shift a').obj X ⟶ (F.shift a'').obj Y`.
-/
lemma shiftIso_hom_app_comp_shiftMap {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn)
    (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    (F.shiftIso n a a' ha').hom.app X ≫ F.shiftMap f a' a'' ha'' =
      (F.shift a).map (f⟦n⟧') ≫ (F.shift a).map ((shiftFunctorAdd' C m n mn hnm).inv.app Y) ≫
        (F.shiftIso mn a a'' (by rw [← ha'', ← ha', ← hnm, add_assoc])).hom.app Y := by
  simp only [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'' Y,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    id_comp, comp_obj, shiftIso_hom_naturality_assoc, shiftMap]

/--
If `f : X ⟶ Y⟦m⟧`, `n + m = 0` and `ha' : m + a = a'`, this lemma relates the two
morphisms `F.shiftMap f a a' ha'` and `(F.shift a').map (f⟦n⟧')`. Indeed,
via canonical isomorphisms, they both identify to morphisms
`(F.shift a).obj X ⟶ (F.shift a').obj Y`.
-/
lemma shiftIso_hom_app_comp_shiftMap_of_add_eq_zero [F.ShiftSequence G]
    {X Y : C} {m : G} (f : X ⟶ Y⟦m⟧)
    (n : G) (hnm : n + m = 0) (a a' : G) (ha' : m + a = a') :
    (F.shiftIso n a' a (by rw [← ha', ← add_assoc, hnm, zero_add])).hom.app X ≫
      F.shiftMap f a a' ha' =
    (F.shift a').map (f⟦n⟧' ≫ (shiftFunctorCompIsoId C m n
      (by rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero])).hom.app Y) := by
  have hnm' : m + n = 0 := by
    rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero]
  dsimp
  simp [F.shiftIso_hom_app_comp_shiftMap f n 0 hnm' a' a, shiftIso_zero_hom_app,
    shiftFunctorCompIsoId]

section

variable [HasZeroMorphisms C] [HasZeroMorphisms A] [F.PreservesZeroMorphisms]
  [∀ (n : M), (shiftFunctor C n).PreservesZeroMorphisms]

instance (n : M) : (F.shift n).PreservesZeroMorphisms :=
  preservesZeroMorphisms_of_iso (F.isoShift n)

@[simp]
lemma shiftMap_zero (X Y : C) (n a a' : M) (ha' : n + a = a') :
    F.shiftMap (0 : X ⟶ Y⟦n⟧) a a' ha' = 0 := by
  simp [shiftMap]

end

section

variable [Preadditive C] [Preadditive A] [F.Additive]
  [∀ (n : M), (shiftFunctor C n).Additive]

instance (n : M) : (F.shift n).Additive := additive_of_iso (F.isoShift n)

end

end

end Functor

end CategoryTheory
