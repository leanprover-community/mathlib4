/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Shift.Pullback
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Tactic.Linarith

/-!
# The (pre)triangulated structure on the opposite category

In this file, we shall construct the (pre)triangulated structure
on the opposite category `Cᵒᵖ` of a (pre)triangulated category `C`.

The shift on `Cᵒᵖ` is obtained by combining the constructions in the files
`CategoryTheory.Shift.Opposite` and `CategoryTheory.Shift.Pullback`.
When the user opens `CategoryTheory.Pretriangulated.Opposite`, the
category `Cᵒᵖ` is equipped with the shift by `ℤ` such that
shifting by `n : ℤ` on `Cᵒᵖ` corresponds to the shift by
`-n` on `C`. This is actually a definitional equality, but the user
should not rely on this, and instead use the isomorphism
`shiftFunctorOpIso C n m hnm : shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op`
where `hnm : n + m = 0`.

Some compatibilities between the shifts on `C` and `Cᵒᵖ` are also expressed through
the equivalence of categories `opShiftFunctorEquivalence C n : Cᵒᵖ ≌ Cᵒᵖ` whose
functor is `shiftFunctor Cᵒᵖ n` and whose inverse functor is `(shiftFunctor C n).op`.

-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category C]

namespace Pretriangulated

variable [HasShift C ℤ]

namespace Opposite

/-- As it is unclear whether the opposite category `Cᵒᵖ` should always be equipped
with the shift by `ℤ` such that shifting by `n` on `Cᵒᵖ` corresponds to shifting
by `-n` on `C`, the user shall have to do `open CategoryTheory.Pretriangulated.Opposite`
in order to get this shift and the (pre)triangulated structure on `Cᵒᵖ`. -/

private abbrev OppositeShiftAux :=
  PullbackShift (OppositeShift C ℤ)
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; linarith))

/-- The category `Cᵒᵖ` is equipped with the shift such that the shift by `n` on `Cᵒᵖ`
corresponds to the shift by `-n` on `C`. -/
noncomputable scoped instance : HasShift Cᵒᵖ ℤ :=
  (inferInstance : HasShift (OppositeShiftAux C) ℤ)

instance [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] (n : ℤ) :
    (shiftFunctor Cᵒᵖ n).Additive :=
  (inferInstance : (shiftFunctor (OppositeShiftAux C) n).Additive)

end Opposite

open Opposite

/-- The shift functor on the opposite category identifies to the opposite functor
of a shift functor on the original category. -/
noncomputable def shiftFunctorOpIso (n m : ℤ) (hnm : n + m = 0) :
    shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op := eqToIso (by
  obtain rfl : m = -n := by linarith
  rfl)

variable {C}

lemma shiftFunctorZero_op_hom_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ ℤ).hom.app X = (shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app X ≫
      ((shiftFunctorZero C ℤ).inv.app X.unop).op := by
  erw [@pullbackShiftFunctorZero_hom_app (OppositeShift C ℤ), oppositeShiftFunctorZero_hom_app]
  rfl

attribute [reassoc] op_comp unop_comp

lemma shiftFunctorZero_op_inv_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ ℤ).inv.app X =
      ((shiftFunctorZero C ℤ).hom.app X.unop).op ≫
      (shiftFunctorOpIso C 0 0 (zero_add 0)).inv.app X := by
  rw [← cancel_epi ((shiftFunctorZero Cᵒᵖ ℤ).hom.app X), Iso.hom_inv_id_app,
    shiftFunctorZero_op_hom_app, assoc, ← op_comp_assoc, Iso.hom_inv_id_app, op_id,
    id_comp, Iso.hom_inv_id_app]

lemma shiftFunctorAdd'_op_hom_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X =
      (shiftFunctorOpIso C _ _ h₃).hom.app X ≫
        ((shiftFunctorAdd' C b₁ b₂ b₃ (by linarith)).inv.app X.unop).op ≫
        (shiftFunctorOpIso C _ _ h₂).inv.app _ ≫
        (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).inv.app X) := by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C ℤ) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; linarith) (by dsimp; linarith) (by dsimp; linarith)]
  erw [oppositeShiftFunctorAdd'_hom_app]
  obtain rfl : b₁ = -a₁ := by linarith
  obtain rfl : b₂ = -a₂ := by linarith
  obtain rfl : b₃ = -a₃ := by linarith
  rfl

lemma shiftFunctorAdd'_op_inv_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).hom.app X) ≫
      (shiftFunctorOpIso C _ _ h₂).hom.app _ ≫
      ((shiftFunctorAdd' C b₁ b₂ b₃ (by linarith)).hom.app X.unop).op ≫
      (shiftFunctorOpIso C _ _ h₃).inv.app X := by
  rw [← cancel_epi ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X), Iso.hom_inv_id_app,
    shiftFunctorAdd'_op_hom_app X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃,
    assoc, assoc, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]
  rw [← op_comp_assoc, Iso.hom_inv_id_app, op_id, id_comp, Iso.hom_inv_id_app]

lemma shiftFunctor_op_map (n m : ℤ) (hnm : n + m = 0) {K L : Cᵒᵖ} (φ : K ⟶ L) :
    (shiftFunctor Cᵒᵖ n).map φ =
      (shiftFunctorOpIso C n m hnm).hom.app K ≫ ((shiftFunctor C m).map φ.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app L :=
  (NatIso.naturality_2 (shiftFunctorOpIso C n m hnm) φ).symm

variable (C)

/-- The autoequivalence `Cᵒᵖ ≌ Cᵒᵖ` whose functor is `shiftFunctor Cᵒᵖ n` and whose inverse
functor is `(shiftFunctor C n).op`. Do not unfold the definitions of the unit and counit
isomorphisms: the compatibilities they satisfy are stated as separate lemmas. -/
@[simps functor inverse]
noncomputable def opShiftFunctorEquivalence (n : ℤ) : Cᵒᵖ ≌ Cᵒᵖ where
  functor := shiftFunctor Cᵒᵖ n
  inverse := (shiftFunctor C n).op
  unitIso := NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg) ≪≫
    isoWhiskerRight (shiftFunctorOpIso C n (-n) n.add_right_neg).symm (shiftFunctor C n).op
  counitIso := isoWhiskerLeft _ (shiftFunctorOpIso C n (-n) n.add_right_neg) ≪≫
    NatIso.op (shiftFunctorCompIsoId C n (-n) n.add_right_neg).symm
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by
    dsimp [shiftFunctorOpIso]
    erw [comp_id, Functor.map_id, comp_id]
    change (shiftFunctorCompIsoId C n (-n) (add_neg_self n)).inv.app (X.unop⟦-n⟧) ≫
      ((shiftFunctorCompIsoId C (-n) n (neg_add_self n)).hom.app X.unop)⟦-n⟧' = 𝟙 _
    rw [shift_shiftFunctorCompIsoId_neg_add_self_hom_app n X.unop, Iso.inv_hom_id_app])

variable {C}

lemma shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n : ℤ) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app X).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app ((Opposite.op ((X.unop)⟦n⟧)))).unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unit_app_inverse X).symm

lemma shift_unop_opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n : ℤ) :
    ((opShiftFunctorEquivalence C n).counitIso.hom.app X).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app ((Opposite.op (X.unop⟦n⟧)))).unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence C n).unitInv_app_inverse X).symm

lemma opShiftFunctorEquivalence_counitIso_inv_app_shift (X : Cᵒᵖ) (n : ℤ) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app X)⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counitInv_app_functor X

lemma opShiftFunctorEquivalence_counitIso_hom_app_shift (X : Cᵒᵖ) (n : ℤ) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app X)⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counit_app_functor X

end Pretriangulated

end CategoryTheory
