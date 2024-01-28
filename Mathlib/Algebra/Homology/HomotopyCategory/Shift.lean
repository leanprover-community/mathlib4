/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.GroupPower.NegOnePow
import Mathlib.CategoryTheory.Shift.Quotient
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Tactic.Linarith

/-!
# The shift on cochain complexes and on the homotopy category

In this file, we show that for any preadditive category `C`, the categories
`CochainComplex C ℤ` and `HomotopyCategory C (ComplexShape.up ℤ)` are
equipped with a shift by `ℤ`.

-/

universe v v' u u'

open CategoryTheory Category Limits

variable (C : Type u) [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] XIsoOfEq_hom_naturality

/-- The shift functor by `n : ℤ` on `CochainComplex C ℤ` which sends a cochain
complex `K` to the complex which is `K.X (i + n)` in degree `i`, and which
multiplies the differentials by `(-1)^n`. -/
@[simps]
def shiftFunctor (n : ℤ) : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K :=
    { X := fun i => K.X (i + n)
      d := fun i j => n.negOnePow • K.d _ _
      d_comp_d' := by
        intros
        simp only [Linear.comp_units_smul, Linear.units_smul_comp, d_comp_d, smul_zero]
      shape := fun i j hij => by
        dsimp
        rw [K.shape, smul_zero]
        intro hij'
        apply hij
        dsimp at hij' ⊢
        linarith }
  map φ :=
    { f := fun i => φ.f _
      comm' := by
        intros
        dsimp
        simp only [Linear.comp_units_smul, Hom.comm, Linear.units_smul_comp] }
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance (n : ℤ) : (shiftFunctor C n).Additive where

variable {C}

/-- The canonical isomorphism `((shiftFunctor C n).obj K).X i ≅ K.X m` when `m = i + n`. -/
@[simp]
def shiftFunctorObjXIso (K : CochainComplex C ℤ) (n i m : ℤ) (hm : m = i + n) :
    ((shiftFunctor C n).obj K).X i ≅ K.X m := K.XIsoOfEq hm.symm

variable (C)

/-- The shift functor by `n` on `CochainComplex C ℤ` identifies to the identity
functor when `n = 0`. -/
@[simps!]
def shiftFunctorZero' (n : ℤ) (h : n = 0) :
    shiftFunctor C n ≅ 𝟭 _ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by linarith))
    (fun _ _ _ => by simp [h])) (by aesop_cat)

/-- The compatibility of the shift functors on `CochainComplex C ℤ` with respect
to the addition of integers. -/
@[simps!]
def shiftFunctorAdd' (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂) :
    shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by linarith))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Linear.units_smul_comp,
        Linear.comp_units_smul, d_comp_XIsoOfEq_hom, smul_smul, XIsoOfEq_hom_comp_d]))
    (by aesop_cat)

attribute [local simp] XIsoOfEq

instance : HasShift (CochainComplex C ℤ) ℤ := hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).Additive :=
  (inferInstance : (CochainComplex.shiftFunctor C n).Additive)

instance {R : Type _} [Ring R] [CategoryTheory.Linear R C] (n : ℤ) :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).Linear R where

variable {C}

@[simp]
lemma shiftFunctor_obj_X' (K : CochainComplex C ℤ) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).X p = K.X (p + n) := rfl

@[simp]
lemma shiftFunctor_map_f' {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map φ).f p = φ.f (p + n) := rfl

lemma shiftFunctor_map_f'' {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n p q : ℤ) (hpq : q = p + n) :
  ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map φ).f p =
    (shiftFunctorObjXIso K n p q hpq).hom ≫ φ.f q ≫ (shiftFunctorObjXIso L n p q hpq).inv := by
  subst hpq
  simp [shiftFunctor_map_f']

@[simp]
lemma shiftFunctor_obj_d' (K : CochainComplex C ℤ) (n i j : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).d i j =
      n.negOnePow • K.d _ _ := rfl

lemma shiftFunctor_obj_d'' (K : CochainComplex C ℤ) (n i j i' j' : ℤ) (hi' : i' = i + n) (hj' : j' = j + n) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).d i j =
      n.negOnePow • (shiftFunctorObjXIso K n i i' hi').hom ≫ K.d i' j' ≫
          (shiftFunctorObjXIso K n j j' hj').inv := by
  subst hi' hj'
  simp

lemma shiftFunctorAdd_inv_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := rfl

lemma shiftFunctorAdd_hom_app_f (K : CochainComplex C ℤ) (a b n : ℤ) :
    ((shiftFunctorAdd (CochainComplex C ℤ) a b).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_comm a, add_assoc])).hom := by
  have : IsIso (((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n) := by
    rw [shiftFunctorAdd_inv_app_f]
    infer_instance
  rw [← cancel_mono (((shiftFunctorAdd (CochainComplex C ℤ) a b).inv.app K).f n),
    ← comp_f, Iso.hom_inv_id_app, id_f, shiftFunctorAdd_inv_app_f]
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl]

lemma shiftFunctorAdd'_inv_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_inv_app_f]

lemma shiftFunctorAdd'_hom_app_f' (K : CochainComplex C ℤ) (a b ab : ℤ) (h : a + b = ab) (n : ℤ) :
    ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b ab h).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [← h, add_assoc, add_comm a])).hom := by
  subst h
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd_hom_app_f]

lemma shiftFunctorZero_inv_app_f (K : CochainComplex C ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := rfl

lemma shiftFunctorZero_hom_app_f (K : CochainComplex C ℤ) (n : ℤ) :
    ((CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K).f n =
      (K.XIsoOfEq (by dsimp; rw [add_zero])).hom := by
  have : IsIso (((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n) := by
    rw [shiftFunctorZero_inv_app_f]
    infer_instance
  rw [← cancel_mono (((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app K).f n), ← comp_f,
    Iso.hom_inv_id_app, id_f, shiftFunctorZero_inv_app_f]
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans, eqToHom_refl]

lemma XIsoOfEq_shift (K : CochainComplex C ℤ) (n : ℤ) {p q : ℤ} (hpq : p = q) :
    (K⟦n⟧).XIsoOfEq hpq = K.XIsoOfEq (show p + n = q + n by rw [hpq]) := rfl

variable (C)

lemma shiftFunctorAdd'_eq (a b c : ℤ) (h : a + b = c) :
    CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) a b c h =
      shiftFunctorAdd' C a b c h := by
  ext
  simp only [shiftFunctorAdd'_hom_app_f', XIsoOfEq, eqToIso.hom, shiftFunctorAdd'_hom_app_f]

lemma shiftFunctorAdd_eq (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (CochainComplex C ℤ) a b = shiftFunctorAdd' C a b _ rfl := by
  rw [← CategoryTheory.shiftFunctorAdd'_eq_shiftFunctorAdd, shiftFunctorAdd'_eq]

lemma shiftFunctorZero_eq :
    CategoryTheory.shiftFunctorZero (CochainComplex C ℤ) ℤ = shiftFunctorZero' C 0 rfl := by
  ext
  rw [shiftFunctorZero_hom_app_f, shiftFunctorZero'_hom_app_f]

variable {C}

lemma shiftFunctorComm_hom_app_f (K : CochainComplex C ℤ) (a b p : ℤ) :
    ((shiftFunctorComm (CochainComplex C ℤ) a b).hom.app K).f p =
      (K.XIsoOfEq (show p + b + a = p + a + b
        by rw [add_assoc, add_comm b, add_assoc])).hom := by
  rw [shiftFunctorComm_eq _ _ _ _ rfl]
  dsimp
  rw [shiftFunctorAdd'_inv_app_f', shiftFunctorAdd'_hom_app_f']
  dsimp [XIsoOfEq]
  apply eqToHom_trans

/-section

variable [HasZeroObject C] (n a a' : ℤ) (ha' : n + a = a')

noncomputable def singleShiftIso_hom_app (X : C) (i : ℤ) :
    (((HomologicalComplex.single C (ComplexShape.up ℤ) a').obj X)⟦n⟧).X i ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj X).X i := by
  by_cases i = a
  · refine' (singleObjXIsoOfEq C (ComplexShape.up ℤ) a' X (i+n) (by linarith)).hom ≫
      (singleObjXIsoOfEq C (ComplexShape.up ℤ) a X i h).inv
  · exact 0

lemma singleShiftIso_hom_app_self (X : C) :
    singleShiftIso_hom_app n a a' ha' X a =
      (shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) a').obj X) n a a' (by linarith)).hom ≫
      (singleObjXSelf C (ComplexShape.up ℤ) a' X).hom ≫
      (singleObjXSelf C (ComplexShape.up ℤ) a X).inv := by
  dsimp [singleShiftIso_hom_app]
  rw [dif_pos rfl]
  dsimp [singleObjXIsoOfEq]
  simp

instance (X : C) (i : ℤ) : IsIso (singleShiftIso_hom_app n a a' ha' X i) := by
  dsimp only [singleShiftIso_hom_app]
  split_ifs with h
  · infer_instance
  · refine' ⟨⟨0, IsZero.eq_of_src _ _ _ , IsZero.eq_of_src _ _ _⟩⟩
    · dsimp
      apply isZeroSingleObjX C (ComplexShape.up ℤ)
      change i + n ≠ a'
      intro h'
      apply h
      linarith
    · exact isZeroSingleObjX C (ComplexShape.up ℤ) _ _ _ h

variable (C)

noncomputable def singleShiftIso [HasZeroObject C] (n a a' : ℤ) (ha' : n + a = a') :
    HomologicalComplex.single C (ComplexShape.up ℤ) a' ⋙
        CategoryTheory.shiftFunctor (CochainComplex C ℤ) n ≅
      HomologicalComplex.single C _ a :=
  NatIso.ofComponents (fun X => HomologicalComplex.Hom.isoOfComponents
    (fun i => asIso (singleShiftIso_hom_app n a a' ha' X i)) (fun _ _ _ => by simp))
    (fun f => by
      ext i
      by_cases i = a
      · subst h
        obtain rfl : i + n = a' := by linarith
        dsimp [singleShiftIso_hom_app, asIso, singleObjXIsoOfEq]
        rw [dif_pos rfl, dif_pos rfl, dif_pos rfl, dif_pos rfl]
        simp
      · dsimp
        rw [dif_neg, dif_neg h, zero_comp, comp_zero]
        intro h'
        apply h
        linarith)

variable {C}

lemma singleShiftIso_hom_app_f [HasZeroObject C] (n a a' : ℤ) (ha' : n + a = a') (X : C) :
  ((singleShiftIso C n a a' ha').hom.app X).f a =
    (shiftFunctorObjXIso ((single C (ComplexShape.up ℤ) a').obj X) n a a' (by linarith)).hom ≫
      (singleObjXSelf C (ComplexShape.up ℤ) a' X).hom ≫ (singleObjXSelf C (ComplexShape.up ℤ) a X).inv := by
  dsimp [singleShiftIso]
  rw [singleShiftIso_hom_app_self]
  rfl

variable (C)

section

variable [HasZeroObject C] (n₁ n₂ n₁₂ : ℤ) (hn₁₂ : n₁ + n₂ = n₁₂) (a₁ a₂ a₃ : ℤ)
  (ha₂ : n₂ + a₁ = a₂) (ha₃ : n₁ + a₂ = a₃)

lemma singleShiftIso_add' : singleShiftIso C n₁₂ a₁ a₃ (by linarith) =
    isoWhiskerLeft _ (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) _ _ _ hn₁₂) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (singleShiftIso C n₁ a₂ a₃ ha₃) _ ≪≫
    singleShiftIso C n₂ a₁ a₂ ha₂ := by
  ext X i
  by_cases a₁ = i
  · subst h
    obtain rfl : a₁ + n₂ = a₂ := by linarith
    dsimp
    simp only [singleShiftIso_hom_app_f, shiftFunctorAdd'_hom_app_f']
    dsimp
    simp only [eqToHom_trans, id_comp]
  · apply IsZero.eq_of_tgt
    dsimp
    split_ifs with h'
    · exfalso
      exact h h'.symm
    · exact isZero_zero _

variable {C}

lemma singleShiftIso_add'_hom_app (X : C) :
  (singleShiftIso C n₁₂ a₁ a₃ (by linarith)).hom.app X =
    (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) _ _ _ hn₁₂).hom.app _ ≫
      ((singleShiftIso C n₁ a₂ a₃ ha₃).hom.app X)⟦n₂⟧' ≫
      (singleShiftIso C n₂ a₁ a₂ ha₂).hom.app X := by
  simp only [singleShiftIso_add' C n₁ n₂ n₁₂ hn₁₂ a₁ a₂ a₃ ha₂ ha₃,
    Iso.trans_hom, isoWhiskerLeft_hom, Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerLeft_app, Functor.associator_inv_app, whiskerRight_app, id_comp]

lemma singleShiftIso_add'_inv_app (X : C) :
  (singleShiftIso C n₁₂ a₁ a₃ (by linarith)).inv.app X =
    (singleShiftIso C n₂ a₁ a₂ ha₂).inv.app X ≫
    ((singleShiftIso C n₁ a₂ a₃ ha₃).inv.app X)⟦n₂⟧' ≫
    (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) _ _ _ hn₁₂).inv.app _ := by
  simp only [singleShiftIso_add' C n₁ n₂ n₁₂ hn₁₂ a₁ a₂ a₃ ha₂ ha₃,
    Iso.trans_inv, isoWhiskerRight_inv, Iso.symm_inv, assoc, isoWhiskerLeft_inv,
    NatTrans.comp_app, whiskerRight_app, Functor.associator_hom_app, whiskerLeft_app, id_comp]

end

end-/

end CochainComplex

namespace CategoryTheory

namespace Functor

variable {C} {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D) [Preadditive D] [F.Additive]

attribute [local simp] Functor.map_zsmul HomologicalComplex.XIsoOfEq

/-- The commutation with the shift isomorphism for the functor on cochain complexes
induced by an additive functor between preadditive categories. -/
@[simps!]
def mapCochainComplexShiftIso (n : ℤ) :
    shiftFunctor _ n ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ shiftFunctor _ n :=
  NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by aesop_cat)) (fun _ => by ext; dsimp; rw [id_comp, comp_id])

instance commShiftMapCochainComplex :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).CommShift ℤ where
  iso := F.mapCochainComplexShiftIso
  zero := by
    ext
    rw [CommShift.isoZero_hom_app]
    dsimp
    simp only [mapCochainComplexShiftIso_hom_app_f, CochainComplex.shiftFunctorZero_inv_app_f,
       CochainComplex.shiftFunctorZero_hom_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
       eqToHom_map, eqToHom_trans, eqToHom_refl]
  add := fun a b => by
    ext
    rw [CommShift.isoAdd_hom_app]
    dsimp
    erw [id_comp, id_comp]
    simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
      CochainComplex.shiftFunctorAdd_inv_app_f, HomologicalComplex.XIsoOfEq, eqToIso,
      eqToHom_map, eqToHom_trans, eqToHom_refl]

--lemma mapHomologicalComplex_commShiftIso_eq (n : ℤ) :
--    (F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n =
--      F.mapCochainComplexShiftIso n := rfl

@[simp]
lemma mapHomologicalComplex_commShiftIso_hom_app_f (K : CochainComplex C ℤ) (n i : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app K).f i = 𝟙 _ := rfl

@[simp]
lemma mapHomologicalComplex_commShiftIso_inv_app_f (K : CochainComplex C ℤ) (n i : ℤ) :
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app K).f i = 𝟙 _ := rfl

end Functor

end CategoryTheory

namespace Homotopy

variable {C}

/-- If `h : Homotopy φ₁ φ₂` and `n : ℤ`, this is the induced homotopy
between `φ₁⟦n⟧'` and `φ₂⟦n⟧'`. -/
def shift {K L : CochainComplex C ℤ} {φ₁ φ₂ : K ⟶ L} (h : Homotopy φ₁ φ₂) (n : ℤ) :
    Homotopy (φ₁⟦n⟧') (φ₂⟦n⟧') where
  hom i j := n.negOnePow • h.hom _ _
  zero i j hij := by
    dsimp
    rw [h.zero, smul_zero]
    intro hij'
    dsimp at hij hij'
    exact hij (by linarith)
  comm := fun i => by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    dsimp
    simpa only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
      Int.units_mul_self, one_smul,
      dNext_eq _ (show (ComplexShape.up ℤ).Rel (i + n) (i + 1 + n) by dsimp; linarith),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1 + n) (i + n) by dsimp; linarith)]
        using h.comm (i + n)

end Homotopy

namespace HomotopyCategory

instance : (homotopic C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ :=
  ⟨fun n _ _ _ _ ⟨h⟩ => ⟨h.shift n⟩⟩

noncomputable instance hasShift :
    HasShift (HomotopyCategory C (ComplexShape.up ℤ)) ℤ := by
  dsimp only [HomotopyCategory]
  infer_instance

noncomputable instance commShiftQuotient :
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)).CommShift ℤ :=
  Quotient.functor_commShift (homotopic C (ComplexShape.up ℤ)) ℤ

instance (n : ℤ) : (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).Additive := by
  have : ((quotient C (ComplexShape.up ℤ) ⋙ shiftFunctor _ n)).Additive := by
    have e := (quotient C (ComplexShape.up ℤ)).commShiftIso n
    exact Functor.additive_of_iso e
  apply Functor.additive_of_full_essSurj_comp (quotient _ _ )

instance {R : Type _} [Ring R] [CategoryTheory.Linear R C] (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).Linear R where
  map_smul := by
    rintro ⟨X⟩ ⟨Y⟩ f r
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective f
    rw [← Functor.map_smul]
    erw [← NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso n) f,
      ← NatIso.naturality_1 ((HomotopyCategory.quotient _ _).commShiftIso n) (r • f)]
    simp only [Functor.comp_obj, Functor.comp_map, Functor.map_smul,
      Linear.smul_comp, Linear.comp_smul]

section

variable {C}
variable {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive]

noncomputable instance : (F.mapHomotopyCategory (ComplexShape.up ℤ)).CommShift ℤ :=
  Quotient.liftCommShift _ _ _ _

instance : NatTrans.CommShift (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom ℤ :=
  Quotient.liftCommShift_compatibility _ _ _ _

end

end HomotopyCategory
