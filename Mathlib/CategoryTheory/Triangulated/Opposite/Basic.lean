/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Shift.Opposite
import Mathlib.CategoryTheory.Shift.Pullback
--import Mathlib.CategoryTheory.Limits.Opposites
--import Mathlib.CategoryTheory.Shift.Opposite
--import Mathlib.CategoryTheory.Shift.Pullback
--import Mathlib.CategoryTheory.Triangulated.Subcategory
--import Mathlib.CategoryTheory.Triangulated.Triangulated
--import Mathlib.CategoryTheory.Triangulated.Adjunction
--import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
--import Mathlib.Tactic.Linarith

/-!
# The shift on the opposite category of a pretriangulated category

Let `C` be a (pre)triangulated category. We already have a shift on `Cᵒᵖ` given
by `CategoryTheory.Shift.Opposite`, but this is not the shift that we want to
make `Cᵒᵖ` into a (pre)triangulated category.
The correct shift on `Cᵒᵖ` is obtained by combining the constructions in the files
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

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category C]

section

variable {C}
variable {D : Type*} [Category D] {F G : C ⥤ D} (e : F ≅ G) (X : C)

@[reassoc (attr := simp)]
lemma Iso.op_hom_inv_id_app : (e.hom.app X).op ≫ (e.inv.app X).op = 𝟙 _ := by
  rw [← op_comp, e.inv_hom_id_app, op_id]

@[reassoc (attr := simp)]
lemma Iso.op_inv_hom_id_app : (e.inv.app X).op ≫ (e.hom.app X).op = 𝟙 _ := by
  rw [← op_comp, e.hom_inv_id_app, op_id]

end

namespace Pretriangulated

variable [HasShift C ℤ]

namespace Opposite

/-- As it is unclear whether the opposite category `Cᵒᵖ` should always be equipped
with the shift by `ℤ` such that shifting by `n` on `Cᵒᵖ` corresponds to shifting
by `-n` on `C`, the user shall have to do `open CategoryTheory.Pretriangulated.Opposite`
in order to get this shift and the (pre)triangulated structure on `Cᵒᵖ`. -/

private abbrev OppositeShiftAux :=
  PullbackShift (OppositeShift C ℤ)
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; omega))

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
  obtain rfl : m = -n := by omega
  rfl)

variable {C}

lemma shiftFunctorZero_op_hom_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ ℤ).hom.app X = (shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app X ≫
      ((shiftFunctorZero C ℤ).inv.app X.unop).op := by
  erw [@pullbackShiftFunctorZero_hom_app (OppositeShift C ℤ), oppositeShiftFunctorZero_hom_app]
  rfl

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
        ((shiftFunctorAdd' C b₁ b₂ b₃ (by omega)).inv.app X.unop).op ≫
        (shiftFunctorOpIso C _ _ h₂).inv.app _ ≫
        (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).inv.app X) := by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C ℤ) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)]
  rw [oppositeShiftFunctorAdd'_hom_app]
  rfl

lemma shiftFunctorAdd'_op_inv_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).hom.app X) ≫
      (shiftFunctorOpIso C _ _ h₂).hom.app _ ≫
      ((shiftFunctorAdd' C b₁ b₂ b₃ (by omega)).hom.app X.unop).op ≫
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

variable (C) in
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
    change (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app (X.unop⟦-n⟧) ≫
      ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app X.unop)⟦-n⟧' = 𝟙 _
    rw [shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app n X.unop, Iso.inv_hom_id_app])

/-! The naturality of the unit and counit isomorphisms are restated in the following
lemmas so as to mitigate the need for `erw`. -/

@[reassoc (attr := simp)]
lemma opShiftFunctorEquivalence_unitIso_hom_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ≫ (opShiftFunctorEquivalence C n).unitIso.hom.app Y =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫ (f⟦n⟧').unop⟦n⟧'.op :=
  (opShiftFunctorEquivalence C n).unitIso.hom.naturality f

@[reassoc (attr := simp)]
lemma opShiftFunctorEquivalence_unitIso_inv_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (f⟦n⟧').unop⟦n⟧'.op ≫ (opShiftFunctorEquivalence C n).unitIso.inv.app Y =
      (opShiftFunctorEquivalence C n).unitIso.inv.app X ≫ f :=
  (opShiftFunctorEquivalence C n).unitIso.inv.naturality f

@[reassoc (attr := simp)]
lemma opShiftFunctorEquivalence_counitIso_hom_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f.unop⟦n⟧'.op⟦n⟧' ≫ (opShiftFunctorEquivalence C n).counitIso.hom.app Y =
      (opShiftFunctorEquivalence C n).counitIso.hom.app X ≫ f :=
  (opShiftFunctorEquivalence C n).counitIso.hom.naturality f

@[reassoc (attr := simp)]
lemma opShiftFunctorEquivalence_counitIso_inv_naturality (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ≫ (opShiftFunctorEquivalence C n).counitIso.inv.app Y =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ f.unop⟦n⟧'.op⟦n⟧' :=
  (opShiftFunctorEquivalence C n).counitIso.inv.naturality f

lemma opShiftFunctorEquivalence_zero_unitIso_hom_app (X : Cᵒᵖ) :
    (opShiftFunctorEquivalence C 0).unitIso.hom.app X =
      ((shiftFunctorZero C ℤ).hom.app X.unop).op ≫
      (((shiftFunctorZero Cᵒᵖ ℤ).inv.app X).unop⟦(0 : ℤ)⟧').op := by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_inv_app, unop_comp, Quiver.Hom.unop_op, Functor.map_comp,
    shiftFunctorCompIsoId_zero_zero_hom_app, assoc]

lemma opShiftFunctorEquivalence_zero_unitIso_inv_app (X : Cᵒᵖ) :
    (opShiftFunctorEquivalence C 0).unitIso.inv.app X =
      (((shiftFunctorZero Cᵒᵖ ℤ).hom.app X).unop⟦(0 : ℤ)⟧').op ≫
        ((shiftFunctorZero C ℤ).inv.app X.unop).op := by
  apply Quiver.Hom.unop_inj
  dsimp [opShiftFunctorEquivalence]
  rw [shiftFunctorZero_op_hom_app, unop_comp, Quiver.Hom.unop_op, Functor.map_comp,
    shiftFunctorCompIsoId_zero_zero_inv_app, assoc]

lemma opShiftFunctorEquivalence_unitIso_hom_app_eq (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p) :
    (opShiftFunctorEquivalence C p).unitIso.hom.app X =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫
      (((opShiftFunctorEquivalence C m).unitIso.hom.app (X⟦n⟧)).unop⟦n⟧').op ≫
      ((shiftFunctorAdd' C m n p h).hom.app _).op ≫
      (((shiftFunctorAdd' Cᵒᵖ n m p (by omega)).inv.app X).unop⟦p⟧').op := by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctorAdd'_op_inv_app _ n m p (by omega) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p), shiftFunctor_op_map _ _ (add_neg_cancel m),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
    id_comp, id_comp, id_comp, comp_id, comp_id]
  dsimp
  rw [comp_id, shiftFunctorCompIsoId_add'_hom_app _ _ _ _ _ _
    (neg_add_cancel m) (neg_add_cancel n) (neg_add_cancel p) h]
  dsimp
  rw [Category.assoc, Category.assoc]
  rfl

lemma opShiftFunctorEquivalence_unitIso_inv_app_eq (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p) :
    (opShiftFunctorEquivalence C p).unitIso.inv.app X =
      (((shiftFunctorAdd' Cᵒᵖ n m p (by omega)).hom.app X).unop⟦p⟧').op ≫
      ((shiftFunctorAdd' C m n p h).inv.app _).op ≫
      (((opShiftFunctorEquivalence C m).unitIso.inv.app (X⟦n⟧)).unop⟦n⟧').op ≫
      (opShiftFunctorEquivalence C n).unitIso.inv.app X := by
  rw [← cancel_mono ((opShiftFunctorEquivalence C p).unitIso.hom.app X), Iso.inv_hom_id_app,
    opShiftFunctorEquivalence_unitIso_hom_app_eq _ _ _ _ h,
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Quiver.Hom.unop_inj
  dsimp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc,
    ← unop_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.op_obj, unop_id,
    Functor.map_id, id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]

lemma opShiftFunctorEquivalence_unitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).unitIso.hom.app X =
      ((shiftFunctorCompIsoId C m n (by omega)).hom.app X.unop).op ≫
        ((shiftFunctorOpIso C n m hnm).inv.app X).unop⟦n⟧'.op := by
  obtain rfl : m = -n := by omega
  rfl

lemma opShiftFunctorEquivalence_unitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).unitIso.inv.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X).unop⟦n⟧'.op ≫
      ((shiftFunctorCompIsoId C m n (by omega)).inv.app X.unop).op := by
  obtain rfl : m = -n := by omega
  rfl

lemma opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app (Opposite.op (X.unop⟦n⟧))) ≫
        ((shiftFunctorCompIsoId C n m hnm).inv.app X.unop).op := by
  obtain rfl : m = -n := by omega
  rfl

lemma opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app X =
      ((shiftFunctorCompIsoId C n m hnm).hom.app X.unop).op ≫
      ((shiftFunctorOpIso C n m hnm).inv.app (Opposite.op (X.unop⟦n⟧))) := by
  obtain rfl : m = -n := by omega
  rfl

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
  ((opShiftFunctorEquivalence C n).counit_app_functor X)

lemma shiftFunctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X)⟦m⟧' ≫
        (shiftFunctorOpIso C m n (by omega)).hom.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorCompIsoId C m n (by omega)).inv.app X.unop).op := by
  dsimp [shiftFunctorCompIsoId]
  simp only [shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by omega) (add_zero 0),
    shiftFunctorZero_op_hom_app X]
  simp only [Functor.op_obj, Opposite.unop_op, Functor.comp_obj,
    NatTrans.naturality_assoc, Functor.op_map, Functor.id_obj,
    Opposite.op_unop, assoc, Iso.inv_hom_id_app_assoc]

lemma shiftFunctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).inv.app X =
      ((shiftFunctorCompIsoId C m n (by omega)).hom.app X.unop).op ≫
      (shiftFunctorOpIso C m n (by omega)).inv.app (Opposite.op (X.unop⟦m⟧)) ≫
      ((shiftFunctorOpIso C n m hnm).inv.app X)⟦m⟧' := by
  dsimp [shiftFunctorCompIsoId]
  simp only [shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by omega) (add_zero 0),
    shiftFunctorZero_op_inv_app X]
  simp only [Functor.id_obj, Opposite.op_unop, Functor.op_obj, Functor.comp_obj, assoc,
    Iso.inv_hom_id_app_assoc]

lemma opShiftFunctorEquivalence_inv_app_shift (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    ((opShiftFunctorEquivalence C m).unitIso.inv.app (X⟦n⟧)) =
      ((shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X).unop⟦m⟧'.op ≫
      ((shiftFunctorOpIso C n m hnm).inv.app X) := by
  rw [shiftFunctorCompIsoId_op_hom_app,
    opShiftFunctorEquivalence_unitIso_inv_app _ m n (by omega)]
  simp only [opShiftFunctorEquivalence_functor, opShiftFunctorEquivalence_inverse,
    Functor.comp_obj, Functor.op_obj,
    Functor.id_obj, Opposite.unop_op, Opposite.op_unop, NatTrans.naturality_assoc,
    Functor.op_map, unop_comp,
    Quiver.Hom.unop_op, assoc, Functor.map_comp, op_comp]
  apply Quiver.Hom.unop_inj
  simp only [Opposite.op_unop, Opposite.unop_op, Quiver.Hom.unop_op, unop_comp, assoc]
  rw [shift_shiftFunctorCompIsoId_inv_app m n (by omega) X.unop]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [← unop_comp_assoc, Iso.hom_inv_id_app, unop_id, id_comp]

lemma natTrans_app_op_shift {D : Type*} [Category D] {F G : Cᵒᵖ ⥤ D} (α : F ⟶ G)
    (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) : α.app (X⟦n⟧) =
      F.map ((shiftFunctorOpIso C n m hnm).hom.app X) ≫ α.app (Opposite.op (X.unop⟦m⟧)) ≫
        G.map ((shiftFunctorOpIso C n m hnm).inv.app X) := by
  rw [← α.naturality, ← F.map_comp_assoc, Iso.hom_inv_id_app, F.map_id, id_comp]

noncomputable def opShiftFunctorEquivalence_symm_homEquiv (n : ℤ) (X Y : Cᵒᵖ) :
    (Opposite.op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧) :=
  (opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv X Y

lemma opShiftFunctorEquivalence_symm_homEquiv_apply {n : ℤ} {X Y : Cᵒᵖ}
    (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    (opShiftFunctorEquivalence_symm_homEquiv n X Y f) =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ (shiftFunctor Cᵒᵖ n).map f := rfl

lemma opShiftFunctorEquivalence_symm_homEquiv_left_inv
    {n : ℤ} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    ((opShiftFunctorEquivalence C n).unitIso.inv.app Y).unop ≫
      (opShiftFunctorEquivalence_symm_homEquiv n X Y f).unop⟦n⟧' = f.unop :=
  Quiver.Hom.op_inj ((opShiftFunctorEquivalence_symm_homEquiv n X Y).left_inv f)

<<<<<<< HEAD:Mathlib/CategoryTheory/Triangulated/Opposite.lean
variable (C)


namespace Opposite

variable (C)

namespace OpOpCommShift

noncomputable def iso (n : ℤ) :
    shiftFunctor C n ⋙ opOp C ≅ opOp C ⋙ shiftFunctor Cᵒᵖᵒᵖ n :=
  NatIso.ofComponents
    (fun X => ((shiftFunctorOpIso C _ _ (neg_add_cancel n)).app (Opposite.op X)).op ≪≫
      (shiftFunctorOpIso Cᵒᵖ _ _ (add_neg_cancel n)).symm.app (Opposite.op (Opposite.op X))) (by
      intros X Y f
      dsimp
      rw [assoc, ← (shiftFunctorOpIso Cᵒᵖ _ _ (add_neg_cancel n)).inv.naturality f.op.op]
      dsimp
      rw [← op_comp_assoc]
      erw [← (shiftFunctorOpIso C _ _ (neg_add_cancel n)).hom.naturality f.op]
      rw [op_comp, assoc])

variable {C}

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive C]

lemma iso_hom_app (X : C) (n m : ℤ) (hnm : n + m = 0) :
    (iso C n).hom.app X =
      ((shiftFunctorOpIso C m n (by omega)).hom.app (Opposite.op X)).op ≫
        (shiftFunctorOpIso Cᵒᵖ _ _ hnm).inv.app (Opposite.op (Opposite.op X)) := by
  obtain rfl : m = -n := by omega
  rfl

lemma iso_inv_app (X : C) (n m : ℤ) (hnm : n + m = 0) :
    (iso C n).inv.app X =
      (shiftFunctorOpIso Cᵒᵖ _ _ hnm).hom.app (Opposite.op (Opposite.op X)) ≫
        ((shiftFunctorOpIso C m n (by omega)).inv.app (Opposite.op X)).op := by
  obtain rfl : m = -n := by omega
  rfl

end OpOpCommShift

noncomputable instance : (opOp C).CommShift ℤ where
  iso n := OpOpCommShift.iso C n
  zero := by
    ext X
    dsimp
    rw [OpOpCommShift.iso_hom_app _ 0 0 (zero_add 0)]
    dsimp
    simp only [Functor.CommShift.isoZero_hom_app, unopUnop_obj, unopUnop_map]
    rw [shiftFunctorZero_op_inv_app, shiftFunctorZero_op_hom_app]
    dsimp
    rw [assoc, ← op_comp_assoc, ← op_comp, Iso.hom_inv_id_app, op_id, op_id, id_comp]
  add a b := by
    ext X
    dsimp
    simp only [Functor.CommShift.isoAdd_hom_app, opOp_obj, Functor.comp_obj, opOp_map,
      OpOpCommShift.iso_hom_app X _ _ (add_neg_cancel (a + b)),
      OpOpCommShift.iso_hom_app _ _ _ (add_neg_cancel a),
      OpOpCommShift.iso_hom_app _ _ _ (add_neg_cancel b),
      shiftFunctor_op_map _ _ (add_neg_cancel b),
      shiftFunctor_op_map _ _ (neg_add_cancel b), assoc,
      ← shiftFunctorAdd'_eq_shiftFunctorAdd,
      shiftFunctorAdd'_op_inv_app (Opposite.op (Opposite.op X))
      a b (a + b) rfl _ _ _ (add_neg_cancel a) (add_neg_cancel b)
      (add_neg_cancel (a+b))]
    simp only [Functor.op_obj, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op,
      Functor.map_comp, op_comp, assoc, Iso.inv_hom_id_app_assoc,
      Iso.op_hom_inv_id_app_assoc]
    simp only [← op_comp_assoc, ← op_comp, assoc, ← Functor.map_comp, ← unop_comp,
      Iso.inv_hom_id_app]
    simp only [Functor.op_obj, Opposite.unop_op, unop_id, id_comp, op_comp, assoc]
    rw [shiftFunctorAdd'_op_hom_app (Opposite.op X) (-a) (-b) (-(a+b)) (by omega)
      _ _ _ (neg_add_cancel a) (neg_add_cancel b) (neg_add_cancel (a + b))]
    simp only [Functor.op_obj, Opposite.unop_op, Functor.comp_obj, op_comp, assoc]
    simp only [← op_comp_assoc, ← op_comp, assoc]
    erw [← NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc]
    simp only [Functor.op_obj, Functor.op_map, op_comp, assoc]
    simp only [← op_comp_assoc, assoc, ← Functor.map_comp_assoc, ← unop_comp,
      Iso.inv_hom_id_app]
    simp only [Functor.op_obj, Opposite.unop_op, unop_id_op, Functor.map_id, id_comp,
      Iso.op_inv_hom_id_app, comp_id]

variable {C}

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive C]

lemma opOp_commShiftIso_hom_app (X : C) (n m : ℤ) (hnm : n + m = 0) :
    ((opOp C).commShiftIso n).hom.app X =
      ((shiftFunctorOpIso C m n (by omega)).hom.app (Opposite.op X)).op ≫
        (shiftFunctorOpIso Cᵒᵖ _ _ hnm).inv.app (Opposite.op (Opposite.op X)) :=
  OpOpCommShift.iso_hom_app _ _ _ hnm

lemma opOp_commShiftIso_inv_app (X : C) (n m : ℤ) (hnm : n + m = 0) :
    ((opOp C).commShiftIso n).inv.app X =
      (shiftFunctorOpIso Cᵒᵖ _ _ hnm).hom.app (Opposite.op (Opposite.op X)) ≫
        ((shiftFunctorOpIso C m n (by omega)).inv.app (Opposite.op X)).op :=
  OpOpCommShift.iso_inv_app _ _ _ hnm

instance : (opOp C).IsTriangulated where
  map_distinguished T hT := by
    rw [mem_distTriang_op_iff']
    refine ⟨_, op_distinguished T hT, ⟨?_⟩⟩
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · aesop_cat
    · aesop_cat
    · dsimp
      simp only [Functor.map_id, comp_id, id_comp,
        opOp_commShiftIso_hom_app T.obj₁ _ _ (add_neg_cancel 1),
        opShiftFunctorEquivalence_counitIso_inv_app _ _ _ (add_neg_cancel 1),
        shiftFunctorCompIsoId_op_hom_app _ _ _ (add_neg_cancel 1),
        shiftFunctor_op_map _ _ (add_neg_cancel 1),
        shiftFunctor_op_map _ _ (neg_add_cancel 1)]
      simp only [Functor.op_obj, Opposite.unop_op, unop_id, Functor.map_id, op_id, id_comp,
        Iso.hom_inv_id_app, comp_id,
        Functor.id_obj, Functor.comp_obj, assoc, Iso.inv_hom_id_app_assoc, op_comp,
        Quiver.Hom.unop_op,
        Iso.op_hom_inv_id_app_assoc, unop_comp, Functor.map_comp]
      slice_rhs 2 3 =>
        rw [← op_comp, ← op_comp, ← Functor.map_comp, ← unop_comp, Iso.inv_hom_id_app]
      simp only [Functor.op_obj, Opposite.unop_op, unop_id, Functor.map_id, op_id, id_comp, assoc]
      slice_rhs 1 2 =>
        rw [← op_comp, ← op_comp]
        erw [← NatTrans.naturality]
      dsimp
      simp only [assoc, shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app]
      slice_rhs 2 3 =>
        rw [← op_comp, ← op_comp, Iso.inv_hom_id_app]
      simp

noncomputable instance : (opOpEquivalence C).inverse.CommShift ℤ :=
  (inferInstance : (opOp C).CommShift ℤ)

noncomputable instance : (opOpEquivalence C).functor.CommShift ℤ :=
  (opOpEquivalence C).commShiftFunctor ℤ

noncomputable instance : (unopUnop C).CommShift ℤ :=
  (inferInstance : (opOpEquivalence C).functor.CommShift ℤ)

instance : (opOpEquivalence C).CommShift ℤ := (opOpEquivalence C).commShift_of_inverse ℤ

instance : (opOpEquivalence C).IsTriangulated :=
  Equivalence.IsTriangulated.mk'' _ (inferInstance : (opOp C).IsTriangulated)

instance : (opOp C).IsTriangulated := inferInstance

instance : (unopUnop C).IsTriangulated :=
  (inferInstance : (opOpEquivalence C).functor.IsTriangulated)

end Opposite

section

variable {J : Type*} (T : J → Triangle C)
  [HasCoproduct (fun j => (T j).obj₁)] [HasCoproduct (fun j => (T j).obj₂)]
  [HasCoproduct (fun j => (T j).obj₃)]
  [HasCoproduct (fun j => (T j).obj₁⟦(1 : ℤ)⟧)]

@[simps!]
noncomputable def coproductTriangle : Triangle C :=
  Triangle.mk (Limits.Sigma.map (fun j => (T j).mor₁))
    (Limits.Sigma.map (fun j => (T j).mor₂))
    (Limits.Sigma.map (fun j => (T j).mor₃) ≫ sigmaComparison _ _)

noncomputable def opCoproductTriangleIsoProductTriangle
  [HasProduct (fun j => ((triangleOpEquivalence C).functor.obj (Opposite.op (T j))).obj₁)]
  [HasProduct (fun j => ((triangleOpEquivalence C).functor.obj (Opposite.op (T j))).obj₂)]
  [HasProduct (fun j => ((triangleOpEquivalence C).functor.obj (Opposite.op (T j))).obj₃)]
  [HasProduct (fun j => (((triangleOpEquivalence C).functor.obj
    (Opposite.op (T j))).obj₁)⟦(1 : ℤ)⟧)] :
    productTriangle (fun j => (triangleOpEquivalence C).functor.obj (Opposite.op (T j))) ≅
    (triangleOpEquivalence C).functor.obj (Opposite.op (coproductTriangle T)) :=
  Triangle.isoMk _ _ (opCoproductIsoProduct (fun j => (T j).obj₃)).symm
    (opCoproductIsoProduct (fun j => (T j).obj₂)).symm
    (opCoproductIsoProduct (fun j => (T j).obj₁)).symm (by
      dsimp [productTriangle]
      simp only [opCoproductIsoProduct_inv_comp_map]) (by
      dsimp [productTriangle]
      simp only [opCoproductIsoProduct_inv_comp_map]) (by
      dsimp [productTriangle]
      have : HasProduct (fun j => (shiftFunctor Cᵒᵖ (1 : ℤ)).obj (Opposite.op (T j).obj₃)) :=
        ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor Cᵒᵖ (1 : ℤ)) _ _
          (productIsProduct (fun j => (Opposite.op (T j).obj₃)))⟩
      rw [assoc, ← cancel_mono ((shiftFunctor Cᵒᵖ (1 : ℤ)).map
        (opCoproductIsoProduct (fun j ↦ (T j).obj₃)).hom), assoc, assoc, assoc, assoc,
        ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, comp_id,
        ← cancel_mono (piComparison (shiftFunctor Cᵒᵖ (1 : ℤ)) (fun j ↦ Opposite.op (T j).obj₃)),
        assoc, assoc, assoc, assoc, IsIso.inv_hom_id, comp_id]
      ext j
      rw [limMap_π, Discrete.natTrans_app, assoc, assoc, assoc, assoc, piComparison_comp_π,
        ← Functor.map_comp, ← Functor.map_comp, assoc,
        opCoproductIsoProduct_hom_comm_π, ← op_comp_assoc, ← op_comp, ι_colimMap_assoc,
        Discrete.natTrans_app, ι_comp_sigmaComparison]
      dsimp
      rw [Functor.map_comp]
      erw [← (opShiftFunctorEquivalence C 1).counitIso.inv.naturality_assoc
        ((Sigma.ι (fun j ↦ (T j).obj₁) j).op)]
      dsimp
      rw [opCoproductIsoProduct_inv_comp_ι_assoc])

lemma coproductTriangle_distinguished (hT : ∀ j, T j ∈ distTriang C) :
    coproductTriangle T ∈ distTriang C := by
  rw [distinguished_iff_op]
  let T' := fun j => (triangleOpEquivalence C).functor.obj (Opposite.op (T j))
  have : HasProduct (fun j ↦ (T' j).obj₁) := by dsimp [T', triangleOpEquivalence]; infer_instance
  have : HasProduct (fun j ↦ (T' j).obj₂) := by dsimp [T', triangleOpEquivalence]; infer_instance
  have : HasProduct (fun j ↦ (T' j).obj₃) := by dsimp [T', triangleOpEquivalence]; infer_instance
  have : HasProduct (fun j ↦ ((T' j).obj₁)⟦(1 : ℤ)⟧) :=
    ⟨_, isLimitFanMkObjOfIsLimit (shiftFunctor Cᵒᵖ (1 : ℤ)) _ _
      (productIsProduct (fun j => (T' j).obj₁))⟩
  exact isomorphic_distinguished _
    (productTriangle_distinguished T' (fun j => op_distinguished _ (hT j))) _
    (opCoproductTriangleIsoProductTriangle T).symm

end

end Pretriangulated

namespace Functor

open Pretriangulated.Opposite Pretriangulated

variable {C}

lemma map_distinguished_op_exact [HasShift C ℤ] [HasZeroObject C] [Preadditive C]
    [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C]{A : Type*} [Category A] [Abelian A] (F : Cᵒᵖ ⥤ A)
    [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).op.map F).Exact :=
  F.map_distinguished_exact _ (op_distinguished T hT)

section

variable {D : Type*} [Category D] [HasShift C ℤ] [HasShift D ℤ]

variable (F : C ⥤ D) [F.CommShift ℤ]

lemma commShift_op_hom_app (n m : ℤ) (hnm : n + m = 0) (X : Cᵒᵖ) :
    (F.op.commShiftIso n).hom.app X =
      (F.map ((shiftFunctorOpIso C n m hnm).hom.app X).unop).op ≫
        ((F.commShiftIso m).inv.app X.unop).op ≫
        (shiftFunctorOpIso D n m hnm).inv.app (Opposite.op (F.obj X.unop)) := by
  obtain rfl : m = -n := by omega
  change _ = (F.map (𝟙 _)).op ≫ _ ≫ 𝟙 _
  rw [F.map_id, op_id, comp_id, id_comp]
  rfl

lemma triangleOpEquivalenceFunctorCompMapTriangleIso_aux (K : Triangle C) :
    (opShiftFunctorEquivalence D 1).counitIso.inv.app (Opposite.op (F.obj K.obj₁)) ≫
      (shiftFunctor Dᵒᵖ (1 : ℤ)).map (((F.commShiftIso 1).hom.app K.obj₁).op ≫ (F.map K.mor₃).op) =
    (F.map (((shiftFunctor Cᵒᵖ (1 : ℤ)).map K.mor₃.op).unop ≫
      ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op K.obj₁)).unop)).op ≫
      (F.op.commShiftIso 1).hom.app (Opposite.op K.obj₃) := by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctor_op_map 1 (-1) (add_neg_cancel 1), op_obj, Opposite.unop_op, unop_comp,
    Quiver.Hom.unop_op, assoc, Iso.inv_hom_id_app_assoc, Iso.unop_hom_inv_id_app_assoc,
    F.commShift_op_hom_app 1 (-1) (add_neg_cancel 1), comp_obj]
  simp only [← op_comp_assoc, assoc, ← F.map_comp]
  simp only [map_comp, assoc, op_comp, Iso.unop_hom_inv_id_app_assoc,
    map_shiftFunctorCompIsoId_hom_app, comp_obj, id_obj, commShiftIso_hom_naturality_assoc,
    Iso.inv_hom_id_app_assoc]

noncomputable def triangleOpEquivalenceFunctorCompMapTriangleIso :
    (triangleOpEquivalence C).functor.rightOp ⋙ F.op.mapTriangle.op ≅
      F.mapTriangle ⋙ (triangleOpEquivalence D).functor.rightOp :=
  NatIso.ofComponents (fun K => Iso.op (by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_
    dsimp
    rw [Functor.map_id, comp_id, id_comp,
      triangleOpEquivalenceFunctorCompMapTriangleIso_aux F K]))
    (fun {K L} φ => Quiver.Hom.unop_inj (by dsimp; aesop_cat))

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [HasZeroObject D] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C][Pretriangulated D]

instance [F.IsTriangulated] : F.op.IsTriangulated where
  map_distinguished T hT := by
    rw [mem_distTriang_op_iff'] at hT
    obtain ⟨T', hT', ⟨e⟩⟩ := hT
    refine Pretriangulated.isomorphic_distinguished _
      (op_distinguished _ (F.map_distinguished _ hT')) _ ?_
    exact F.op.mapTriangle.mapIso e ≪≫
      Iso.unop (F.triangleOpEquivalenceFunctorCompMapTriangleIso.symm.app T')

end


end Functor

namespace Triangulated

open Pretriangulated.Opposite Pretriangulated

variable {C}
variable [HasShift C ℤ] [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

namespace Subcategory

def op (S : Subcategory C) : Subcategory (Cᵒᵖ) where
  P := fun X => S.P X.unop
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Opposite.op Z, hZ.op, hZ'⟩
  shift X n hX := S.shift _ (-n) hX
  ext₂' := by
    rintro T hT h₁ h₃
    rw [mem_distTriang_op_iff] at hT
    obtain ⟨X, hX, ⟨e⟩⟩ := S.ext₂' _ hT h₃ h₁
    exact ⟨Opposite.op X, hX, ⟨e.symm.op⟩⟩

def unop (S : Subcategory Cᵒᵖ) : Subcategory C where
  P := fun X => S.P (Opposite.op X)
  zero' := by
    obtain ⟨Z, hZ, hZ'⟩ := S.zero'
    exact ⟨Z.unop, hZ.unop, hZ'⟩
  shift X n hX := by
    obtain ⟨m, rfl⟩ : ∃ m, n = -m := ⟨-n, by simp⟩
    exact S.shift _ m hX
  ext₂' := by
    rintro T hT h₁ h₃
    obtain ⟨X, hX, ⟨e⟩⟩ := S.ext₂' _ (op_distinguished _ hT) h₃ h₁
    exact ⟨Opposite.unop X, hX, ⟨e.symm.unop⟩⟩

@[simp] lemma unop_op (S : Subcategory C) : S.op.unop = S := rfl
@[simp] lemma op_unop (S : Subcategory Cᵒᵖ) : S.unop.op = S := rfl

instance (S : Subcategory C) [ClosedUnderIsomorphisms S.P] :
    ClosedUnderIsomorphisms S.op.P where
  of_iso e := mem_of_iso S.P e.symm.unop

instance (S : Subcategory Cᵒᵖ) [ClosedUnderIsomorphisms S.P] :
    ClosedUnderIsomorphisms S.unop.P where
  of_iso e := mem_of_iso S.P e.symm.op

lemma W_of_op (S : Subcategory C) {X Y : C} (f : X ⟶ Y) (hf : S.op.W f.op) : S.W f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [Subcategory.W_iff']
  exact ⟨_, _, _, Pretriangulated.unop_distinguished _ h₁, h₂⟩

lemma W_of_unop (S : Subcategory Cᵒᵖ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (hf : S.unop.W f.unop) : S.W f := by
  obtain ⟨Z, a, b, h₁, h₂⟩ := hf
  rw [Subcategory.W_iff']
  exact ⟨_, _, _, Pretriangulated.op_distinguished _ h₁, h₂⟩

lemma W_op_iff (S : Subcategory C) {X Y : Cᵒᵖ } (f : X ⟶ Y) :
    S.op.W f ↔ S.W f.unop :=
  ⟨S.W_of_op _, S.op.W_of_unop _⟩

lemma W_op (S : Subcategory C) : S.op.W = S.W.op := by
  ext X Y f
  apply S.W_op_iff

end Subcategory

end Triangulated

=======
end Pretriangulated

>>>>>>> origin/jriou_localization_bump_deps:Mathlib/CategoryTheory/Triangulated/Opposite/Basic.lean

end CategoryTheory
