/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.GroupPower.NegOnePow
import Mathlib.CategoryTheory.Shift.Quotient
import Mathlib.Tactic.Linarith

/-!
# The shift on cochain complexes and on the homotopy category

In this file, we show that for any preadditive category `C`, the categories
`CochainComplex C ℤ` and `HomotopyCategory C (ComplexShape.up ℤ)` are
equipped with a shift by `ℤ`.

-/

universe v v' u u'

open CategoryTheory

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
        simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, d_comp_d, smul_zero]
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
        simp only [Preadditive.comp_zsmul, Hom.comm, Preadditive.zsmul_comp] }
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
def shiftFunctorAdd' (n₁ n₂ n₁₂ : ℤ) (h : n₁ + n₂ = n₁₂ ) :
    shiftFunctor C n₁₂ ≅ shiftFunctor C n₁ ⋙ shiftFunctor C n₂ :=
  NatIso.ofComponents (fun K => Hom.isoOfComponents
    (fun i => K.shiftFunctorObjXIso _ _ _ (by linarith))
    (fun _ _ _ => by
      subst h
      dsimp
      simp only [add_comm n₁ n₂, Int.negOnePow_add, Preadditive.zsmul_comp,
        Preadditive.comp_zsmul, d_comp_XIsoOfEq_hom, smul_smul, XIsoOfEq_hom_comp_d]))
    (by aesop_cat)

attribute [local simp] XIsoOfEq

instance : HasShift (CochainComplex C ℤ) ℤ := hasShiftMk _ _
  { F := shiftFunctor C
    zero := shiftFunctorZero' C _ rfl
    add := fun n₁ n₂ => shiftFunctorAdd' C n₁ n₂ _ rfl }

instance (n : ℤ) :
    (CategoryTheory.shiftFunctor (HomologicalComplex C (ComplexShape.up ℤ)) n).Additive :=
  (inferInstance : (CochainComplex.shiftFunctor C n).Additive)

variable {C}

@[simp]
lemma shiftFunctor_map_f' {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n p : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map φ).f p = φ.f (p+n) := rfl

@[simp]
lemma shiftFunctor_obj_d' (K : CochainComplex C ℤ) (n i j : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj K).d i j =
      n.negOnePow • K.d _ _ := rfl

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
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

end CochainComplex

namespace CategoryTheory

open Category

namespace Functor

variable {C}
variable (F : C ⥤ D) [F.Additive]

attribute [local simp] Functor.map_zsmul

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

lemma mapHomologicalComplex_commShiftIso_eq (n : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n =
      F.mapCochainComplexShiftIso n := rfl

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
    rw [h.zero, zsmul_zero]
    intro hij'
    dsimp at hij hij'
    exact hij (by linarith)
  comm := fun i => by
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
    dsimp
    simpa only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul,
      Int.negOnePow_mul_self, one_smul,
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

end HomotopyCategory
