/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.NatIso

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

@[expose] public section

namespace CategoryTheory

open Category

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
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

/-- For any functor `F : C ⥤ D` and any `a` in `A` such that `a = 0`,
this is the obvious isomorphism `shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` deduced from the
isomorphisms `shiftFunctorZero'` on both categories `C` and `D`. -/
@[simps!]
noncomputable def isoZero' (a : A) (ha : a = 0) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  isoWhiskerRight (shiftFunctorZero' C a ha) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero' D a ha).symm

@[simp]
lemma isoZero'_eq_isoZero : isoZero' F A 0 rfl = isoZero F A := by
  ext; simp [isoZero', shiftFunctorZero']

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

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma isoAdd_hom_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).hom.app X =
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) := by
  simp only [isoAdd, isoAdd'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma isoAdd_inv_app {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.isoAdd e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        (shiftFunctor D b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) := by
  simp only [isoAdd, isoAdd'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

set_option backward.isDefEq.respectTransparency false in
lemma isoAdd'_isoZero {a : A}
    (e : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) :
    isoAdd' (add_zero a) e (isoZero F A) = e := by
  ext X
  simp [shiftFunctorAdd'_add_zero_hom_app, ← Functor.map_comp_assoc,
    shiftFunctorAdd'_add_zero_inv_app]

set_option backward.isDefEq.respectTransparency false in
lemma isoZero_isoAdd'_ {a : A}
    (e : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) :
    isoAdd' (zero_add a) (isoZero F A) e = e := by
  ext X
  have := e.hom.naturality ((shiftFunctorZero C A).inv.app X)
  dsimp at this
  simp [shiftFunctorAdd'_zero_add_hom_app,
    shiftFunctorAdd'_zero_add_inv_app, ← map_comp,
    reassoc_of% this]

set_option backward.isDefEq.respectTransparency false in
lemma isoAdd'_assoc {a b c ab bc abc : A}
    (ea : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (eb : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (ec : shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c)
    (hab : a + b = ab) (hbc : b + c = bc) (h : a + b + c = abc) :
    isoAdd' (show ab + c = abc by rwa [← hab]) (isoAdd' hab ea eb) ec =
      isoAdd' (show a + bc = abc by grind) ea (isoAdd' hbc eb ec) := by
  ext X
  have := NatTrans.naturality_2 ec.hom ((shiftFunctorAdd' C a b ab hab).app X)
  dsimp at this ⊢
  simp only [isoAdd'_hom_app, Category.assoc]
  rw [← NatTrans.naturality_assoc, ← this, Category.assoc, ← F.map_comp_assoc,
    shiftFunctorAdd'_assoc_hom_app a b c ab bc abc hab hbc h,
    Functor.map_comp_assoc, Category.assoc]
  simp_rw [← Functor.map_comp_assoc]
  simp [shiftFunctorAdd'_assoc_inv_app a b c ab bc abc hab hbc h]

end CommShift

/-- A functor `F` commutes with the shift by a monoid `A` if it is equipped with
commutation isomorphisms with the shifts by all `a : A`, and these isomorphisms
satisfy coherence properties with respect to `0 : A` and the addition in `A`. -/
class CommShift (F : C ⥤ D) (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] where
  /-- The commutation isomorphisms for all `a`-shifts this functor is equipped with -/
  commShiftIso (F) (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  commShiftIso_zero (F) (A) : commShiftIso 0 = CommShift.isoZero F A := by cat_disch
  commShiftIso_add (F) (a b : A) :
    commShiftIso (a + b) = CommShift.isoAdd (commShiftIso a) (commShiftIso b) := by cat_disch

variable {A}

export CommShift (commShiftIso commShiftIso_zero commShiftIso_add)

@[deprecated (since := "2025-11-11")] alias CommShift.iso := commShiftIso
@[deprecated (since := "2025-11-11")] alias CommShift.zero := commShiftIso_zero
@[deprecated (since := "2025-11-11")] alias CommShift.add := commShiftIso_add

section

variable [F.CommShift A]

-- Note: The following two lemmas are introduced in order to have more proofs work `by simp`.
-- Indeed, `simp only [(F.commShiftIso a).hom.naturality f]` would almost never work because
-- of the compositions of functors which appear in both the source and target of
-- `F.commShiftIso a`. Otherwise, we would be forced to use `erw [NatTrans.naturality]`.

@[reassoc (attr := simp)]
lemma commShiftIso_hom_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    dsimp% F.map (f⟦a⟧') ≫ (F.commShiftIso a).hom.app Y =
      (F.commShiftIso a).hom.app X ≫ (F.map f)⟦a⟧' :=
  (F.commShiftIso a).hom.naturality f

@[reassoc (attr := simp)]
lemma commShiftIso_inv_naturality {X Y : C} (f : X ⟶ Y) (a : A) :
    dsimp% (F.map f)⟦a⟧' ≫ (F.commShiftIso a).inv.app Y =
      (F.commShiftIso a).inv.app X ≫ F.map (f⟦a⟧') :=
  (F.commShiftIso a).inv.naturality f

-- The next two lemmas are added to ease automation. They could be proven by `simp`
-- using `set_option backward.isDefEq.respectTransparency false`

@[reassoc (attr := simp)]
lemma commShiftIso_hom_inv_id_app (X : C) (a : A) :
    dsimp% (F.commShiftIso a).hom.app X ≫ (F.commShiftIso a).inv.app X = 𝟙 _ :=
  (F.commShiftIso a).hom_inv_id_app X

@[reassoc (attr := simp)]
lemma commShiftIso_inv_hom_id_app (X : C) (a : A) :
    dsimp% (F.commShiftIso a).inv.app X ≫ (F.commShiftIso a).hom.app X = 𝟙 _ :=
  (F.commShiftIso a).inv_hom_id_app X

variable (A) in
set_option linter.docPrime false in
lemma commShiftIso_zero' (a : A) (h : a = 0) :
    F.commShiftIso a = CommShift.isoZero' F A a h := by
  subst h; rw [CommShift.isoZero'_eq_isoZero, commShiftIso_zero]

lemma commShiftIso_add' {a b c : A} (h : a + b = c) :
    F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.commShiftIso b) := by
  subst h
  simp only [commShiftIso_add, CommShift.isoAdd]

end

namespace CommShift

set_option backward.isDefEq.respectTransparency false in
variable (C) in
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]
instance id : CommShift (𝟭 C) A where
  commShiftIso := fun _ => rightUnitor _ ≪≫ (leftUnitor _).symm

set_option backward.isDefEq.respectTransparency false in
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app]
instance comp [F.CommShift A] [G.CommShift A] : (F ⋙ G).CommShift A where
  commShiftIso a := (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.commShiftIso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso a) ≪≫
    (Functor.associator _ _ _).symm
  commShiftIso_zero := by
    ext X
    dsimp
    simp only [id_comp, comp_id, commShiftIso_zero, isoZero_hom_app, ← Functor.map_comp_assoc,
      assoc, Iso.inv_hom_id_app, id_obj, comp_map, comp_obj]
  commShiftIso_add := fun a b => by
    ext X
    dsimp
    simp only [commShiftIso_add, isoAdd_hom_app]
    dsimp
    simp only [comp_id, id_comp, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, comp_obj]
    simp only [map_comp, assoc, commShiftIso_hom_naturality_assoc]

end CommShift

alias commShiftIso_id_hom_app := CommShift.id_commShiftIso_hom_app
alias commShiftIso_id_inv_app := CommShift.id_commShiftIso_inv_app
alias commShiftIso_comp_hom_app := CommShift.comp_commShiftIso_hom_app
alias commShiftIso_comp_inv_app := CommShift.comp_commShiftIso_inv_app

attribute [simp] commShiftIso_id_hom_app commShiftIso_id_inv_app

variable {B}

set_option backward.isDefEq.respectTransparency false in
lemma map_shiftFunctorComm_hom_app [F.CommShift B] (X : C) (a b : B) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) := by
  have eq := NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add a b)) X
  simp only [comp_obj, CommShift.isoAdd_hom_app,
    ← cancel_epi (F.map ((shiftFunctorAdd C a b).inv.app X)),
    ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp] at eq
  simp only [shiftFunctorComm_eq D a b _ rfl]
  dsimp
  simp only [shiftFunctorAdd'_eq_shiftFunctorAdd, Category.assoc,
    ← reassoc_of% eq, shiftFunctorComm_eq C a b _ rfl]
  dsimp
  rw [Functor.map_comp]
  simp only [NatTrans.congr_app (congr_arg Iso.hom (F.commShiftIso_add' (add_comm b a))) X,
    CommShift.isoAdd'_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, Category.id_comp, comp_obj, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

namespace NatTrans

variable {C D E J : Type*} [Category* C] [Category* D] [Category* E] [Category* J]
  {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) (e : F₁ ≅ F₂)
    (G G' : D ⥤ E) (τ'' : G ⟶ G') (H : E ⥤ J)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [HasShift J A]
  [F₁.CommShift A] [F₂.CommShift A] [F₃.CommShift A]
    [G.CommShift A] [G'.CommShift A] [H.CommShift A]

variable {A} in
/-- Auxiliary structure for `NatTrans.CommShift` when we need to
show a compatibility of a natural transformation `τ : F₁ ⟶ F₂` with
respect to the shift by a specific element `a`. See also
`NatTrans.CommShift.of_core` -/
structure CommShiftCore (a : A) : Prop where
  shift_comm : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
    Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom

namespace CommShiftCore

attribute [reassoc] shift_comm

section

variable {A} {a : A} (hτ : CommShiftCore τ a)

include hτ

@[reassoc]
lemma shift_app_comm (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  congr_app hτ.shift_comm X

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shift_app (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← hτ.shift_app_comm, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma app_shift (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  simp [hτ.shift_app_comm_assoc τ X]

end

variable {τ}

set_option backward.isDefEq.respectTransparency false in
lemma zero : CommShiftCore τ (0 : A) where
  shift_comm := by
    ext X
    simp [Functor.commShiftIso_zero, ← NatTrans.naturality]

variable {A}

set_option backward.isDefEq.respectTransparency false in
lemma add {a b : A} (ha : CommShiftCore τ a) (hb : CommShiftCore τ b) :
    CommShiftCore τ (a + b) where
  shift_comm := by
    ext X
    have := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
    dsimp at this ⊢
    simp only [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app,
      ← NatTrans.naturality_2 τ ((shiftFunctorAdd C a b).app X),
      Functor.comp_obj, hb.app_shift_assoc, ha.app_shift, assoc,
      (shiftFunctor D b).map_comp_assoc]
    simp [← Functor.map_comp_assoc, this]

end CommShiftCore

/-- If `τ : F₁ ⟶ F₂` is a natural transformation between two functors
which commute with a shift by an additive monoid `A`, this typeclass
asserts a compatibility of `τ` with these shifts. -/
class CommShift : Prop where
  shift_comm (a : A) : (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
    Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by cat_disch

section

variable {A}

variable {τ} in
lemma CommShift.of_core (h : ∀ (a : A), CommShiftCore τ a) :
    CommShift τ A where
  shift_comm a := (h a).shift_comm

variable [NatTrans.CommShift τ A]

@[reassoc]
lemma shift_comm (a : A) :
    (F₁.commShiftIso a).hom ≫ Functor.whiskerRight τ _ =
      Functor.whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by
  apply CommShift.shift_comm

@[reassoc]
lemma shift_app_comm (a : A) (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  congr_app (shift_comm τ a) X

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma shift_app (a : A) (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← shift_app_comm, Iso.inv_hom_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma app_shift (a : A) (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  simp [shift_app_comm_assoc τ a X]

end

namespace CommShift

instance of_iso_inv [NatTrans.CommShift e.hom A] :
    NatTrans.CommShift e.inv A := ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧)), e.hom_inv_id_app_assoc, ← shift_app_comm_assoc,
    ← Functor.map_comp, e.hom_inv_id_app, Functor.map_id, Category.comp_id]⟩

instance of_iso_symm [NatTrans.CommShift e.hom A] : NatTrans.CommShift e.symm.hom A :=
  NatTrans.CommShift.of_iso_inv e A

lemma of_isIso [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (inv τ) A := by
  haveI : NatTrans.CommShift (asIso τ).hom A := by assumption
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

variable (F₁) in
instance id : NatTrans.CommShift (𝟙 F₁) A where

attribute [local simp] Functor.commShiftIso_comp_hom_app
  shift_app_comm shift_app_comm_assoc

set_option backward.isDefEq.respectTransparency false in
instance comp [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A] :
    NatTrans.CommShift (τ ≫ τ') A where

set_option backward.isDefEq.respectTransparency false in
instance whiskerRight [NatTrans.CommShift τ A] :
    NatTrans.CommShift (Functor.whiskerRight τ G) A := ⟨fun a => by
  ext X
  simp only [Functor.whiskerRight_twice, comp_app, Functor.commShiftIso_comp_hom_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, comp_id, id_comp, assoc, ← Functor.commShiftIso_hom_naturality, ←
    G.map_comp_assoc, shift_app_comm, Functor.whiskerLeft_app]⟩

set_option backward.isDefEq.respectTransparency false in
instance whiskerLeft [NatTrans.CommShift τ'' A] :
    NatTrans.CommShift (Functor.whiskerLeft F₁ τ'') A where

instance associator : CommShift (Functor.associator F₁ G H).hom A where

instance leftUnitor : CommShift F₁.leftUnitor.hom A where

instance rightUnitor : CommShift F₁.rightUnitor.hom A where

end CommShift

end NatTrans

namespace Functor

namespace CommShift

variable {C D E : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : C ⥤ D} (e : F ≅ G)
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]
  [F.CommShift A]

set_option backward.isDefEq.respectTransparency false in
/-- If `e : F ≅ G` is an isomorphism of functors and if `F` commutes with the
shift, then `G` also commutes with the shift. -/
@[simps! -isSimp commShiftIso_hom_app commShiftIso_inv_app, implicit_reducible]
def ofIso : G.CommShift A where
  commShiftIso a := isoWhiskerLeft _ e.symm ≪≫ F.commShiftIso a ≪≫ isoWhiskerRight e _
  commShiftIso_zero := by
    ext X
    simp [F.commShiftIso_zero, ← NatTrans.naturality]
  commShiftIso_add a b := by
    ext X
    simp only [comp_obj, F.commShiftIso_add, Iso.trans_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
      isoAdd_hom_app, whiskerRight_app, assoc, map_comp, NatTrans.naturality_assoc,
      NatIso.cancel_natIso_inv_left]
    simp only [← Functor.map_comp_assoc, e.hom_inv_id_app_assoc]
    simp only [← NatTrans.naturality, comp_obj, comp_map, map_comp, assoc]

lemma ofIso_compatibility :
    letI := ofIso e A
    NatTrans.CommShift e.hom A := by
  letI := ofIso e A
  exact ⟨fun a => by ext; simp [ofIso_commShiftIso_hom_app]⟩

end CommShift

end Functor

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {A : Type*}

section hasShiftOfFullyFaithful

variable [AddMonoid A] [HasShift D A]
  {F : C ⥤ D} (hF : F.FullyFaithful)
  (s : A → C ⥤ C) (i : ∀ i, s i ⋙ F ≅ F ⋙ shiftFunctor D i)

namespace CommShift

set_option backward.isDefEq.respectTransparency false in
/-- If `F : C ⥤ D` is a fully faithful functor which is used
to construct a shift by `A` on `C` from a shift on `D`,
then the functor `F` itself commutes with the shift by `A`. -/
@[implicit_reducible]
def ofHasShiftOfFullyFaithful :
    letI := hF.hasShift s i; F.CommShift A := by
  letI := hF.hasShift s i
  exact
  { commShiftIso := i
    commShiftIso_zero := by
      ext X
      simp [ShiftMkCore.shiftFunctorZero_eq]
    commShiftIso_add := fun a b => by
      ext X
      simp [ShiftMkCore.shiftFunctorAdd_eq, ShiftMkCore.shiftFunctor_eq,
        ← Functor.map_comp_assoc] }

end CommShift

lemma shiftFunctorIso_ofHasShiftOfFullyFaithful (a : A) :
    letI := hF.hasShift s i
    letI := CommShift.ofHasShiftOfFullyFaithful hF s i
    F.commShiftIso a = i a := by
  rfl

end hasShiftOfFullyFaithful

@[reassoc]
lemma map_shiftFunctorComm
    [AddCommMonoid A] [HasShift C A] [HasShift D A]
    (F : C ⥤ D) [F.CommShift A] (X : C) (a b : A) :
    F.map ((shiftFunctorComm C a b).hom.app X) = (F.commShiftIso b).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦b⟧' ≫ (shiftFunctorComm D a b).hom.app (F.obj X) ≫
      ((F.commShiftIso b).inv.app X)⟦a⟧' ≫ (F.commShiftIso a).inv.app (X⟦b⟧) :=
  map_shiftFunctorComm_hom_app _ _ _ _

namespace CommShift

variable {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  [Full G] [Faithful G]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A]
  [G.CommShift A] [H.CommShift A]

namespace OfComp

variable {A}

/-- Auxiliary definition for `Functor.CommShift.ofComp`. -/
noncomputable def iso (a : A) : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  ((whiskeringRight C D E).obj G).preimageIso
    (Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e ≪≫
      H.commShiftIso a ≪≫ isoWhiskerRight e.symm _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F (G.commShiftIso a).symm ≪≫ (Functor.associator _ _ _).symm)

@[simp, reassoc]
lemma map_iso_hom_app (a : A) (X : C) :
    G.map ((iso e a).hom.app X) = e.hom.app (X⟦a⟧) ≫
      (H.commShiftIso a).hom.app X ≫ (e.inv.app X)⟦a⟧' ≫
      (G.commShiftIso a).inv.app (F.obj X) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).hom = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

@[simp, reassoc]
lemma map_iso_inv_app (a : A) (X : C) :
    G.map ((iso e a).inv.app X) =
      (G.commShiftIso a).hom.app (F.obj X) ≫ (e.hom.app X)⟦a⟧' ≫
      (H.commShiftIso a).inv.app X ≫ e.inv.app (X⟦a⟧) := by
  have h : ((whiskeringRight C D E).obj G).map (iso e a).inv = _ :=
    Functor.map_preimage _ _
  simpa using congr_app h X

attribute [irreducible] iso

end OfComp

set_option backward.isDefEq.respectTransparency false in
/-- Given an isomorphism `e : F ⋙ G ≅ H` where `G` is fully faithful,
the functor `F` commutes with shifts by `A` if `G` and `H` do. -/
@[implicit_reducible]
noncomputable def ofComp : F.CommShift A where
  commShiftIso := OfComp.iso e
  commShiftIso_zero := by
    ext X
    apply G.map_injective
    simp [G.commShiftIso_zero, H.commShiftIso_zero]
  commShiftIso_add a b := by
    ext X
    apply G.map_injective
    simp only [comp_obj, OfComp.map_iso_hom_app, H.commShiftIso_add, isoAdd_hom_app,
      G.commShiftIso_add, isoAdd_inv_app, NatTrans.naturality_assoc, comp_map, assoc,
      Iso.inv_hom_id_app_assoc, map_comp]
    simp only [← NatTrans.naturality_assoc, ← commShiftIso_inv_naturality_assoc,
      ← Functor.map_comp_assoc]
    congr 4
    simp

set_option backward.isDefEq.respectTransparency false in
lemma ofComp_compatibility :
    letI := ofComp e
    NatTrans.CommShift e.hom A := by
  letI := ofComp e
  refine ⟨fun a ↦ ?_⟩
  ext X
  simp [commShiftIso_comp_hom_app, show F.commShiftIso a = OfComp.iso e a from rfl,
    ← Functor.map_comp]

end CommShift

end Functor

/--
Assume that we have a diagram of categories
```
C₁ ⥤ D₁
‖     ‖
v     v
C₂ ⥤ D₂
‖     ‖
v     v
C₃ ⥤ D₃
```
with functors `F₁₂ : C₁ ⥤ C₂`, `F₂₃ : C₂ ⥤ C₃` and `F₁₃ : C₁ ⥤ C₃` on the first
column that are related by a natural transformation `α : F₁₃ ⟶ F₁₂ ⋙ F₂₃`
and similarly `β : G₁₂ ⋙ G₂₃ ⟶ G₁₃` on the second column. Assume that we have
natural transformations
`e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂` (top square), `e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃` (bottom square),
and `e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃` (outer square), where the horizontal functors
are denoted `L₁`, `L₂` and `L₃`. Assume that `e₁₃` is determined by the other
natural transformations `α`, `e₂₃`, `e₁₂` and `β`. Then, if all these categories
are equipped with a shift by an additive monoid `A`, and all these functors commute with
these shifts, then the natural transformation `e₁₃` of the outer square commutes with the
shift if all `α`, `e₂₃`, `e₁₂` and `β` do. -/
lemma NatTrans.CommShift.verticalComposition {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* D₁] [Category* D₂] [Category* D₃]
    {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₁₃ : C₁ ⥤ C₃} (α : F₁₃ ⟶ F₁₂ ⋙ F₂₃)
    {G₁₂ : D₁ ⥤ D₂} {G₂₃ : D₂ ⥤ D₃} {G₁₃ : D₁ ⥤ D₃} (β : G₁₂ ⋙ G₂₃ ⟶ G₁₃)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃}
    (e₁₂ : F₁₂ ⋙ L₂ ⟶ L₁ ⋙ G₁₂) (e₂₃ : F₂₃ ⋙ L₃ ⟶ L₂ ⋙ G₂₃) (e₁₃ : F₁₃ ⋙ L₃ ⟶ L₁ ⋙ G₁₃)
    (A : Type*) [AddMonoid A] [HasShift C₁ A] [HasShift C₂ A] [HasShift C₃ A]
    [HasShift D₁ A] [HasShift D₂ A] [HasShift D₃ A]
    [F₁₂.CommShift A] [F₂₃.CommShift A] [F₁₃.CommShift A] [CommShift α A]
    [G₁₂.CommShift A] [G₂₃.CommShift A] [G₁₃.CommShift A] [CommShift β A]
    [L₁.CommShift A] [L₂.CommShift A] [L₃.CommShift A]
    [CommShift e₁₂ A] [CommShift e₂₃ A]
    (h₁₃ : e₁₃ = Functor.whiskerRight α L₃ ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F₁₂ e₂₃ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight e₁₂ G₂₃ ≫ (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L₁ β) : CommShift e₁₃ A := by
  subst h₁₃
  infer_instance

end CategoryTheory
