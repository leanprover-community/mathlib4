/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.Shift.Basic

/-!
# Functors which commute with shifts

Let `C` and `D` be two categories equipped with shifts by an additive monoid `A`. In this file,
we define the notion of functor `F : C ⥤ D` which "commutes" with these shifts. The associated
type class is `[F.CommShift A]`. The data consists of commutation isomorphisms
`F.commShiftIso a : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` for all `a : A`
which satisfy a compatibility with the addition and the zero. After this was formalised in Lean,
it was found that this definition is exactly the definition which appears in Jean-Louis
Verdier's thesis (I 1.2.3/1.2.4), although the language is different. (In Verdier's thesis,
the shift is not given by a monoidal functor `Discrete A ⥤ C ⥤ C`, but by a fibred
category `C ⥤ BA`, where `BA` is the category with one object, the endomorphisms of which
identify to `A`. The choice of a cleavage for this fibered category gives the individual
shift functors.)

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category

namespace Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (A B : Type*) [AddMonoid A] [AddCommMonoid B]
  [HasShift C A] [HasShift D A] [HasShift E A]
  [HasShift C B] [HasShift D B]

namespace CommShift

/-- For any functor `F : C ⥤ D`, this is the obvious isomorphism
`shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A)` deduced from the
isomorphisms `shiftFunctorZero` on both categories `C` and `D`. -/
@[simps!]
noncomputable def isoZero : shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A) :=
  isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

variable {F A}

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by `c` when
`a + b = c`. -/
@[simps!]
noncomputable def isoAdd' {a b c : A} (h : a + b = c)
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c :=
  isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

/-- If a functor `F : C ⥤ D` is equipped with "commutation isomorphisms" with the
shifts by `a` and `b`, then there is a commutation isomorphism with the shift by `a + b`. -/
noncomputable def isoAdd {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C (a + b) ⋙ F ≅ F ⋙ shiftFunctor D (a + b) :=
  CommShift.isoAdd' rfl e₁ e₂

@[simp]
lemma isoAdd_hom_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).hom.app X =
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) := by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]
lemma isoAdd_inv_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        (shiftFunctor D b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) := by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

end CommShift

/-- A functor `F` commutes with the shift by a monoid `A` if it is equipped with
commutation isomorphisms with the shifts by all `a : A`, and these isomorphisms
satisfy coherence properties with respect to `0 : A` and the addition in `A`. -/
class CommShift where
  iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  zero : iso 0 = CommShift.isoZero F A := by aesop_cat
  add (a b : A) : iso (a + b) = CommShift.isoAdd (iso a) (iso b) := by aesop_cat

variable {A}

section

variable [F.CommShift A]

/-- If a functor `F` commutes with the shift by `A` (i.e. `[F.CommShift A]`), then
`F.commShiftIso a` is the given isomorphism `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a`. -/
def commShiftIso (a : A) :
    shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  CommShift.iso a

-- Note: The following two lemmas are introduced in order to have more proofs work `by simp`.
-- Indeed, `simp only [(F.commShiftIso a).hom.naturality f]` would almost never work because
-- of the compositions of functors which appear in both the source and target of
-- `F.commShiftIso a`. Otherwise, we would be forced to use `erw [NatTrans.naturality]`.

@[reassoc (attr := simp)]
lemma commShiftIso_hom_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    F.map (f⟦a⟧') ≫ (F.commShiftIso a).hom.app Y =
      (F.commShiftIso a).hom.app X ≫ (F.map f)⟦a⟧' :=
  (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]
lemma commShiftIso_inv_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    (F.map f)⟦a⟧' ≫ (F.commShiftIso a).inv.app Y =
      (F.commShiftIso a).inv.app X ≫ F.map (f⟦a⟧') :=
  (F.commShiftIso a).inv.naturality f

variable (A)

lemma commShiftIso_zero :
    F.commShiftIso (0 : A) = CommShift.isoZero F A :=
  CommShift.zero

variable {A}

lemma commShiftIso_add (a b : A) :
    F.commShiftIso (a + b) = CommShift.isoAdd (F.commShiftIso a) (F.commShiftIso b) :=
  CommShift.add a b

lemma commShiftIso_add' {a b c : A} (h : a + b = c) :
    F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.commShiftIso b) := by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

end

namespace CommShift

variable (C)

instance id : CommShift (𝟭 C) A where
  iso := fun a => rightUnitor _ ≪≫ (leftUnitor _).symm

end CommShift

variable {B}

lemma map_shiftFunctorComm_hom_app [F.CommShift B] (X : C) (a b : B) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) := by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)), Category.assoc,
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp, F.map_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [Functor.map_comp, shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq, shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, comp_obj, Category.comp_id]

@[simp, reassoc]
lemma map_shiftFunctorCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).hom.app X) =
      (F.commShiftIso b).hom.app (X⟦a⟧) ≫ ((F.commShiftIso a).hom.app X)⟦b⟧' ≫
        (shiftFunctorCompIsoId D a b h).hom.app (F.obj X) := by
  dsimp [shiftFunctorCompIsoId]
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' h)) X
  simp only [commShiftIso_zero, comp_obj, CommShift.isoZero_hom_app,
    CommShift.isoAdd'_hom_app] at eq
  rw [← cancel_epi (F.map ((shiftFunctorAdd' C a b 0 h).hom.app X)), ← reassoc_of% eq, F.map_comp]
  simp only [Iso.inv_hom_id_app, id_obj, Category.comp_id, ← F.map_comp_assoc, Iso.hom_inv_id_app,
    F.map_id, Category.id_comp]

@[simp, reassoc]
lemma map_shiftFunctorCompIsoId_inv_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) :
    F.map ((shiftFunctorCompIsoId C a b h).inv.app X) =
      (shiftFunctorCompIsoId D a b h).inv.app (F.obj X) ≫
        ((F.commShiftIso a).inv.app X)⟦b⟧' ≫ (F.commShiftIso b).inv.app (X⟦a⟧) := by
  rw [← cancel_epi (F.map ((shiftFunctorCompIsoId C a b h).hom.app X)), ← F.map_comp,
    Iso.hom_inv_id_app, F.map_id, map_shiftFunctorCompIsoId_hom_app]
  simp only [comp_obj, id_obj, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp]

end Functor

end CategoryTheory
