/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Shift.Opposite
public import Mathlib.CategoryTheory.Shift.Pullback

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

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive ZeroObject

variable (C : Type*) [Category* C]

namespace Pretriangulated

variable [HasShift C ℤ]

namespace Opposite

/-- As it is unclear whether the opposite category `Cᵒᵖ` should always be equipped
with the shift by `ℤ` such that shifting by `n` on `Cᵒᵖ` corresponds to shifting
by `-n` on `C`, the user shall have to do `open CategoryTheory.Pretriangulated.Opposite`
in order to get this shift and the (pre)triangulated structure on `Cᵒᵖ`. -/
private abbrev OppositeShiftAux :=
  PullbackShift (OppositeShift C ℤ)
    (AddMonoidHom.mk' (fun (n : ℤ) => -n) (by intros; dsimp; lia))

/-- The category `Cᵒᵖ` is equipped with the shift such that the shift by `n` on `Cᵒᵖ`
corresponds to the shift by `-n` on `C`. -/
scoped instance : HasShift Cᵒᵖ ℤ :=
  (inferInstance : HasShift (OppositeShiftAux C) ℤ)

instance [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] (n : ℤ) :
    (shiftFunctor Cᵒᵖ n).Additive :=
  (inferInstance : (shiftFunctor (OppositeShiftAux C) n).Additive)

end Opposite

open Opposite

/-- The shift functor on the opposite category identifies to the opposite functor
of a shift functor on the original category. -/
def shiftFunctorOpIso (n m : ℤ) (hnm : n + m = 0) :
    shiftFunctor Cᵒᵖ n ≅ (shiftFunctor C m).op := eqToIso (by
  obtain rfl : m = -n := by lia
  rfl)

variable {C}

lemma shiftFunctorZero_op_hom_app (X : Cᵒᵖ) :
    (shiftFunctorZero Cᵒᵖ ℤ).hom.app X = (shiftFunctorOpIso C 0 0 (zero_add 0)).hom.app X ≫
      ((shiftFunctorZero C ℤ).inv.app X.unop).op := rfl

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
        ((shiftFunctorAdd' C b₁ b₂ b₃ (by lia)).inv.app X.unop).op ≫
        (shiftFunctorOpIso C _ _ h₂).inv.app _ ≫
        (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).inv.app X) := by
  erw [@pullbackShiftFunctorAdd'_hom_app (OppositeShift C ℤ) _ _ _ _ _ _ _ X
    a₁ a₂ a₃ h b₁ b₂ b₃ (by dsimp; lia) (by dsimp; lia) (by dsimp; lia)]
  rw [oppositeShiftFunctorAdd'_hom_app]
  rfl

lemma shiftFunctorAdd'_op_inv_app (X : Cᵒᵖ) (a₁ a₂ a₃ : ℤ) (h : a₁ + a₂ = a₃)
    (b₁ b₂ b₃ : ℤ) (h₁ : a₁ + b₁ = 0) (h₂ : a₂ + b₂ = 0) (h₃ : a₃ + b₃ = 0) :
    (shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).inv.app X =
      (shiftFunctor Cᵒᵖ a₂).map ((shiftFunctorOpIso C _ _ h₁).hom.app X) ≫
      (shiftFunctorOpIso C _ _ h₂).hom.app _ ≫
      ((shiftFunctorAdd' C b₁ b₂ b₃ (by lia)).hom.app X.unop).op ≫
      (shiftFunctorOpIso C _ _ h₃).inv.app X := by
  rw [← cancel_epi ((shiftFunctorAdd' Cᵒᵖ a₁ a₂ a₃ h).hom.app X), Iso.hom_inv_id_app,
    shiftFunctorAdd'_op_hom_app X a₁ a₂ a₃ h b₁ b₂ b₃ h₁ h₂ h₃,
    assoc, assoc, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]
  rw [← op_comp_assoc, Iso.hom_inv_id_app, op_id, id_comp, Iso.hom_inv_id_app]

lemma shiftFunctor_op_map {K L : Cᵒᵖ} (φ : K ⟶ L) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (shiftFunctor Cᵒᵖ n).map φ =
      (shiftFunctorOpIso C n m hnm).hom.app K ≫ ((shiftFunctor C m).map φ.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app L :=
  (NatIso.naturality_2 (shiftFunctorOpIso C n m hnm) φ).symm

variable (C) in
/-- The autoequivalence `Cᵒᵖ ≌ Cᵒᵖ` whose functor is `shiftFunctor Cᵒᵖ n` and whose inverse
functor is `(shiftFunctor C n).op`. In most cases, it is not necessary to unfold the
definitions of the unit and counit isomorphisms: the compatibilities they satisfy
are stated as separate lemmas. -/
@[simps functor inverse]
def opShiftFunctorEquivalence (n : ℤ) : Cᵒᵖ ≌ Cᵒᵖ where
  functor := shiftFunctor Cᵒᵖ n
  inverse := (shiftFunctor C n).op
  unitIso := NatIso.op (shiftFunctorCompIsoId C (-n) n n.add_left_neg) ≪≫
    Functor.isoWhiskerRight (shiftFunctorOpIso C n (-n) n.add_right_neg).symm (shiftFunctor C n).op
  counitIso := Functor.isoWhiskerLeft _ (shiftFunctorOpIso C n (-n) n.add_right_neg) ≪≫
    NatIso.op (shiftFunctorCompIsoId C n (-n) n.add_right_neg).symm
  functor_unitIso_comp X := Quiver.Hom.unop_inj (by
    dsimp [shiftFunctorOpIso]
    erw [comp_id, Functor.map_id, comp_id]
    change (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app (X.unop⟦-n⟧) ≫
      ((shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).hom.app X.unop)⟦-n⟧' = 𝟙 _
    rw [shift_shiftFunctorCompIsoId_neg_add_cancel_hom_app n X.unop, Iso.inv_hom_id_app])

@[reassoc]
lemma opShiftFunctorEquivalence_unitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).unitIso.hom.app X =
      ((shiftFunctorCompIsoId C m n (by lia)).hom.app X.unop).op ≫
        (((shiftFunctorOpIso C n m hnm).inv.app (X)).unop⟦n⟧').op := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
lemma opShiftFunctorEquivalence_unitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).unitIso.inv.app X =
      (((shiftFunctorOpIso C n m hnm).hom.app (X)).unop⟦n⟧').op ≫
      ((shiftFunctorCompIsoId C m n (by lia)).inv.app X.unop).op := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
lemma opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app X =
      (shiftFunctorOpIso C n m hnm).hom.app (Opposite.op (X.unop⟦n⟧)) ≫
        ((shiftFunctorCompIsoId C n m hnm).inv.app X.unop).op
        := by
  obtain rfl : m = -n := by lia
  rfl

@[reassoc]
lemma opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app X =
      ((shiftFunctorCompIsoId C n m hnm).hom.app X.unop).op ≫
        (shiftFunctorOpIso C n m hnm).inv.app (Opposite.op (X.unop⟦n⟧)) := by
  obtain rfl : m = -n := by lia
  rfl

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

lemma opShiftFunctorEquivalence_add_unitIso_hom_app_eq
    (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.hom.app X =
      (opShiftFunctorEquivalence C n).unitIso.hom.app X ≫
      (((opShiftFunctorEquivalence C m).unitIso.hom.app (X⟦n⟧)).unop⟦n⟧').op ≫
      ((shiftFunctorAdd' C m n p h).hom.app _).op ≫
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).inv.app X).unop⟦p⟧').op := by
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctorAdd'_op_inv_app _ n m p (by lia) _ _ _ (add_neg_cancel n)
    (add_neg_cancel m) (add_neg_cancel p), shiftFunctor_op_map _ m (-m),
    Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [Functor.map_id, Functor.map_id, Functor.map_id, Functor.map_id,
    id_comp, id_comp, id_comp, comp_id, comp_id]
  dsimp
  rw [comp_id, shiftFunctorCompIsoId_add'_hom_app _ _ _ _ _ _
    (neg_add_cancel m) (neg_add_cancel n) (neg_add_cancel p) h]
  dsimp
  rw [Category.assoc, Category.assoc]
  rfl

lemma opShiftFunctorEquivalence_add_unitIso_inv_app_eq
    (X : Cᵒᵖ) (m n p : ℤ) (h : m + n = p := by lia) :
    (opShiftFunctorEquivalence C p).unitIso.inv.app X =
      (((shiftFunctorAdd' Cᵒᵖ n m p (by lia)).hom.app X).unop⟦p⟧').op ≫
      ((shiftFunctorAdd' C m n p h).inv.app _).op ≫
      (((opShiftFunctorEquivalence C m).unitIso.inv.app (X⟦n⟧)).unop⟦n⟧').op ≫
      (opShiftFunctorEquivalence C n).unitIso.inv.app X := by
  rw [← cancel_mono ((opShiftFunctorEquivalence C p).unitIso.hom.app X), Iso.inv_hom_id_app,
    opShiftFunctorEquivalence_add_unitIso_hom_app_eq _ _ _ _ h,
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Quiver.Hom.unop_inj
  dsimp
  simp only [Category.assoc,
    ← unop_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.op_obj, unop_id,
    Functor.map_id, id_comp, ← Functor.map_comp, Iso.hom_inv_id_app]

@[deprecated (since := "2025-12-08")] alias opShiftFunctorEquivalence_unitIso_hom_app_eq :=
  opShiftFunctorEquivalence_add_unitIso_hom_app_eq
@[deprecated (since := "2025-12-08")] alias opShiftFunctorEquivalence_unitIso_inv_app_eq :=
  opShiftFunctorEquivalence_add_unitIso_inv_app_eq

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

@[reassoc]
lemma shiftFunctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X)⟦m⟧' ≫
        (shiftFunctorOpIso C m n (by lia)).hom.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorCompIsoId C m n (by lia)).inv.app X.unop).op := by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_hom_app X,
    shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by lia) (add_zero 0)]

@[reassoc]
lemma shiftFunctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0 := by lia) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).inv.app X =
      ((shiftFunctorCompIsoId C m n (by omega)).hom.app X.unop).op ≫
        (shiftFunctorOpIso C m n (by omega)).inv.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorOpIso C n m hnm).inv.app X)⟦m⟧' := by
  simp [shiftFunctorCompIsoId, shiftFunctorZero_op_inv_app X,
    shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by omega) (add_zero 0)]

@[reassoc]
lemma shift_opShiftFunctorEquivalence_counitIso_inv_app
    (X : C) (m n : ℤ) (hmn : m + n = 0 := by lia) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app (Opposite.op X))⟦m⟧' =
      (opShiftFunctorEquivalence C n).counitIso.inv.app ((Opposite.op X)⟦m⟧) ≫
        (((shiftFunctorOpIso C m n hmn).hom.app (Opposite.op X)).unop⟦n⟧').op⟦n⟧' ≫
          ((shiftFunctorOpIso C m n hmn).inv.app (Opposite.op (X⟦n⟧)))⟦n⟧' ≫
            (shiftFunctorComm Cᵒᵖ n m).inv.app (Opposite.op (X⟦n⟧)) := by
  obtain rfl : m = -n := by lia
  dsimp [opShiftFunctorEquivalence]
  simp only [shiftFunctor_op_map _ (-n) n, shiftFunctor_op_map _ n (-n),
    shiftFunctorComm_inv_app_of_add_eq_zero n (-n) (by lia), assoc,
    shiftFunctorCompIsoId_op_inv_app, shiftFunctorCompIsoId_op_hom_app,
    shift_shiftFunctorCompIsoId_hom_app, op_comp, unop_comp, Quiver.Hom.unop_op,
    Functor.map_comp, Iso.inv_hom_id_app_assoc, Functor.op_obj]
  apply Quiver.Hom.unop_inj
  dsimp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.unop_hom_inv_id_app_assoc]
  congr 3
  exact (NatIso.naturality_1 (shiftFunctorCompIsoId C n (-n) (by lia)) _).symm

/-- Given objects `X` and `Y` in `Cᵒᵖ`, this is the bijection
`(op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧)` for any `n : ℤ`. -/
def opShiftFunctorEquivalenceSymmHomEquiv {n : ℤ} {X Y : Cᵒᵖ} :
    (Opposite.op (X.unop⟦n⟧) ⟶ Y) ≃ (X ⟶ Y⟦n⟧) :=
  (opShiftFunctorEquivalence C n).symm.toAdjunction.homEquiv X Y

@[reassoc]
lemma opShiftFunctorEquivalenceSymmHomEquiv_apply {n : ℤ} {X Y : Cᵒᵖ}
    (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    opShiftFunctorEquivalenceSymmHomEquiv f =
      (opShiftFunctorEquivalence C n).counitIso.inv.app X ≫ (shiftFunctor Cᵒᵖ n).map f := rfl

@[reassoc]
lemma opShiftFunctorEquivalenceSymmHomEquiv_left_inv
    {n : ℤ} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    ((opShiftFunctorEquivalence C n).unitIso.inv.app Y).unop ≫
      (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' = f.unop :=
  Quiver.Hom.op_inj (opShiftFunctorEquivalenceSymmHomEquiv.left_inv f)

@[reassoc]
lemma shift_opShiftFunctorEquivalenceSymmHomEquiv_unop
    {n : ℤ} {X Y : Cᵒᵖ} (f : Opposite.op (X.unop⟦n⟧) ⟶ Y) :
    (opShiftFunctorEquivalenceSymmHomEquiv f).unop⟦n⟧' =
      ((opShiftFunctorEquivalence C n).unitIso.hom.app Y).unop ≫ f.unop := by
  rw [← opShiftFunctorEquivalenceSymmHomEquiv_left_inv]
  simp

end Pretriangulated

end CategoryTheory
