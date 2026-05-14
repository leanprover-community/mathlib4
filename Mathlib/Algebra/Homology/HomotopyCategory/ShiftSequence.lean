/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.InducedShiftSequence
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Data.Int.Order.Units
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-! # Compatibilities of the homology functor with the shift

This file studies how homology of cochain complexes behaves with respect to
the shift: there is a natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a`
when `n + a = a'`. This is summarized by instances
`(homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ` in the `CochainComplex`
and `HomotopyCategory` namespaces.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category ComplexShape Limits

variable (C : Type*) [Category* C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex

attribute [local simp] XIsoOfEq_hom_naturality smul_smul

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism `(K⟦n⟧).sc' i j k ≅ K.sc' i' j' k'` when `n + i = i'`,
`n + j = j'` and `n + k = k'`. -/
@[simps!]
def shiftShortComplexFunctor' (n i j k i' j' k' : ℤ)
    (hi : n + i = i') (hj : n + j = j') (hk : n + k = k') :
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n) ⋙ shortComplexFunctor' C _ i j k ≅
      shortComplexFunctor' C _ i' j' k' :=
  NatIso.ofComponents (fun K => ShortComplex.isoMk
      (n.negOnePow • ((shiftEval C n i i' hi).app K))
      ((shiftEval C n j j' hj).app K) (n.negOnePow • ((shiftEval C n k k' hk).app K))
      (by simp) (by simp))
      (fun f ↦ by ext <;> simp)

/-- The natural isomorphism `(K⟦n⟧).sc i ≅ K.sc i'` when `n + i = i'`. -/
@[simps!]
noncomputable def shiftShortComplexFunctorIso (n i i' : ℤ) (hi : n + i = i') :
    shiftFunctor C n ⋙ shortComplexFunctor C _ i ≅ shortComplexFunctor C _ i' :=
  shiftShortComplexFunctor' C n _ i _ _ i' _
    (by simp only [prev]; lia) hi (by simp only [next]; lia)

variable {C}

set_option backward.isDefEq.respectTransparency false in
lemma shiftShortComplexFunctorIso_zero_add_hom_app (a : ℤ) (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C 0 a a (zero_add a)).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) := by
  ext <;> simp [one_smul, shiftFunctorZero_hom_app_f]

set_option backward.isDefEq.respectTransparency false in
lemma shiftShortComplexFunctorIso_add'_hom_app
    (n m mn : ℤ) (hmn : m + n = mn) (a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'')
    (K : CochainComplex C ℤ) :
    (shiftShortComplexFunctorIso C mn a a'' (by rw [← ha'', ← ha', ← add_assoc, hmn])).hom.app K =
      (shortComplexFunctor C (ComplexShape.up ℤ) a).map
        ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n mn hmn).hom.app K) ≫
        (shiftShortComplexFunctorIso C n a a' ha').hom.app (K⟦m⟧) ≫
        (shiftShortComplexFunctorIso C m a' a'' ha'').hom.app K := by
  ext <;> dsimp <;> simp only [← hmn, Int.negOnePow_add, shiftFunctorAdd'_hom_app_f',
    XIsoOfEq_shift, Linear.comp_units_smul, Linear.units_smul_comp,
    XIsoOfEq_hom_comp_XIsoOfEq_hom, smul_smul]

variable [CategoryWithHomology C]

namespace ShiftSequence

variable (C) in
/-- The natural isomorphism `(K⟦n⟧).homology a ≅ K.homology a'` when `n + a = a'`. -/
noncomputable def shiftIso (n a a' : ℤ) (ha' : n + a = a') :
    (CategoryTheory.shiftFunctor _ n) ⋙ homologyFunctor C (ComplexShape.up ℤ) a ≅
      homologyFunctor C (ComplexShape.up ℤ) a' :=
  Functor.isoWhiskerLeft _ (homologyFunctorIso C (ComplexShape.up ℤ) a) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (shiftShortComplexFunctorIso C n a a' ha')
      (ShortComplex.homologyFunctor C) ≪≫
    (homologyFunctorIso C (ComplexShape.up ℤ) a').symm

lemma shiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (shiftIso C n a a' ha').hom.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').hom.app K) := by
  simp [shiftIso, HomologicalComplex.homology]

lemma shiftIso_inv_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    (shiftIso C n a a' ha').inv.app K =
      ShortComplex.homologyMap ((shiftShortComplexFunctorIso C n a a' ha').inv.app K) := by
  simp [shiftIso, HomologicalComplex.homology]

end ShiftSequence

set_option backward.isDefEq.respectTransparency false in
noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ where
  sequence n := homologyFunctor C (ComplexShape.up ℤ) n
  isoZero := Iso.refl _
  shiftIso n a a' ha' := ShiftSequence.shiftIso C n a a' ha'
  shiftIso_zero a := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, comp_id,
      shiftShortComplexFunctorIso_zero_add_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext K
    dsimp [homologyMap]
    simp only [ShiftSequence.shiftIso_hom_app, id_comp,
      ← ShortComplex.homologyMap_comp, shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftShortComplexFunctorIso_add'_hom_app n m _ rfl a a' a'' ha' ha'' K]

lemma quasiIsoAt_shift_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n i j : ℤ) (h : n + i = j) :
    QuasiIsoAt (φ⟦n⟧') i ↔ QuasiIsoAt φ j := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (NatIso.isIso_map_iff
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n i j h) φ)

lemma quasiIso_shift_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
    QuasiIso (φ⟦n⟧') ↔ QuasiIso φ := by
  simp only [quasiIso_iff, fun i ↦ quasiIsoAt_shift_iff φ n i _ rfl]
  constructor
  · intro h j
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by lia⟩
    exact h i
  · intro h i
    exact h (n + i)

instance {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) [QuasiIso φ] :
    QuasiIso (φ⟦n⟧') := by
  rw [quasiIso_shift_iff]
  infer_instance

instance : (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).IsCompatibleWithShift ℤ where
  condition n := by ext; apply quasiIso_shift_iff

variable (C) in
lemma homologyFunctor_shift (n : ℤ) :
    (homologyFunctor C (ComplexShape.up ℤ) 0).shift n =
      homologyFunctor C (ComplexShape.up ℤ) n := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma liftCycles_shift_homologyπ
    (K : CochainComplex C ℤ) {A : C} {n i : ℤ} (f : A ⟶ (K⟦n⟧).X i) (j : ℤ)
    (hj : (up ℤ).next i = j) (hf : f ≫ (K⟦n⟧).d i j = 0) (i' : ℤ) (hi' : n + i = i') (j' : ℤ)
    (hj' : (up ℤ).next i' = j') :
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i =
      K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom) j' hj' (by
        simp only [next] at hj hj'
        obtain rfl : i' = i + n := by lia
        obtain rfl : j' = j + n := by lia
        dsimp at hf ⊢
        simp only [Linear.comp_units_smul] at hf
        apply (one_smul (M := ℤˣ) _).symm.trans _
        rw [← Int.units_mul_self n.negOnePow, mul_smul, comp_id, hf, smul_zero]) ≫
        K.homologyπ i' ≫
          ((HomologicalComplex.homologyFunctor C (up ℤ) 0).shiftIso n i i' hi').inv.app K := by
  simp only [liftCycles, homologyπ,
    shiftFunctorObjXIso, Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    ShiftSequence.shiftIso_inv_app, ShortComplex.homologyπ_naturality,
    ShortComplex.liftCycles_comp_cyclesMap_assoc, shiftShortComplexFunctorIso_inv_app_τ₂,
    assoc, Iso.hom_inv_id, comp_id]
  rfl

end CochainComplex

namespace HomotopyCategory

variable [CategoryWithHomology C]

noncomputable instance :
    (homologyFunctor C (ComplexShape.up ℤ) 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.induced (homologyFunctorFactors C (ComplexShape.up ℤ) 0) ℤ
    (homologyFunctor C (ComplexShape.up ℤ))
    (homologyFunctorFactors C (ComplexShape.up ℤ))

variable {C}

lemma homologyShiftIso_hom_app (n a a' : ℤ) (ha' : n + a = a') (K : CochainComplex C ℤ) :
    ((homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app
      ((quotient _ _).obj K) =
    (homologyFunctor _ _ a).map (((quotient _ _).commShiftIso n).inv.app K) ≫
      (homologyFunctorFactors _ _ a).hom.app (K⟦n⟧) ≫
      ((HomologicalComplex.homologyFunctor _ _ 0).shiftIso n a a' ha').hom.app K ≫
      (homologyFunctorFactors _ _ a').inv.app K := by
  apply Functor.ShiftSequence.induced_shiftIso_hom_app_obj

@[reassoc]
lemma homologyFunctor_shiftMap
    {K L : CochainComplex C ℤ} {n : ℤ} (f : K ⟶ L⟦n⟧) (a a' : ℤ) (h : n + a = a') :
    (homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap
      (ShiftedHom.map f (quotient _ _)) a a' h =
        (homologyFunctorFactors _ _ a).hom.app K ≫
          (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftMap f a a' h ≫
            (homologyFunctorFactors _ _ a').inv.app L := by
  apply Functor.ShiftSequence.induced_shiftMap

end HomotopyCategory
