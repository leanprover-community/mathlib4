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
  erw [@pullbackShiftFunctorZero_hom_app (OppositeShift C ℤ) _ _ _ _ _ _ _ X,
    oppositeShiftFunctorZero_hom_app]
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
functor is `(shiftFunctor C n).op`. -/
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

lemma opShiftFunctorEquivalence_unitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).unitIso.hom.app X =
      ((shiftFunctorCompIsoId C m n (by linarith)).hom.app X.unop).op ≫
        ((shiftFunctorOpIso C n m hnm).inv.app X).unop⟦n⟧'.op := by
  obtain rfl : m = -n := by linarith
  rfl

lemma opShiftFunctorEquivalence_unitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).unitIso.inv.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X).unop⟦n⟧'.op ≫
      ((shiftFunctorCompIsoId C m n (by linarith)).inv.app X.unop).op := by
  obtain rfl : m = -n := by linarith
  rfl

lemma opShiftFunctorEquivalence_counitIso_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app (Opposite.op (X.unop⟦n⟧))) ≫
        ((shiftFunctorCompIsoId C n m hnm).inv.app X.unop).op := by
  obtain rfl : m = -n := by linarith
  rfl

lemma opShiftFunctorEquivalence_counitIso_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (opShiftFunctorEquivalence C n).counitIso.inv.app X =
      ((shiftFunctorCompIsoId C n m hnm).hom.app X.unop).op ≫
      ((shiftFunctorOpIso C n m hnm).inv.app (Opposite.op (X.unop⟦n⟧))) := by
  obtain rfl : m = -n := by linarith
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
  ((opShiftFunctorEquivalence C n).counitInv_app_functor X)

lemma opShiftFunctorEquivalence_counitIso_hom_app_shift (X : Cᵒᵖ) (n : ℤ) :
    (opShiftFunctorEquivalence C n).counitIso.hom.app (X⟦n⟧) =
      ((opShiftFunctorEquivalence C n).unitIso.inv.app X)⟦n⟧' :=
  ((opShiftFunctorEquivalence C n).counit_app_functor X)

lemma shiftFunctorCompIsoId_op_hom_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X =
      ((shiftFunctorOpIso C n m hnm).hom.app X)⟦m⟧' ≫
        (shiftFunctorOpIso C m n (by linarith)).hom.app (Opposite.op (X.unop⟦m⟧)) ≫
          ((shiftFunctorCompIsoId C m n (by linarith)).inv.app X.unop).op := by
  dsimp [shiftFunctorCompIsoId]
  simp only [shiftFunctorAdd'_op_inv_app X n m 0 hnm m n 0 hnm (by linarith) (add_zero 0),
    shiftFunctorZero_op_hom_app X]
  simp only [Functor.op_obj, Opposite.unop_op, Functor.comp_obj,
    NatTrans.naturality_assoc, Functor.op_map, Functor.id_obj,
    Opposite.op_unop, assoc, Iso.inv_hom_id_app_assoc]

lemma shiftFunctorCompIsoId_op_inv_app (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    (shiftFunctorCompIsoId Cᵒᵖ n m hnm).inv.app X =
      ((shiftFunctorCompIsoId C m n (by linarith)).hom.app X.unop).op ≫
      (shiftFunctorOpIso C m n (by linarith)).inv.app (Opposite.op (X.unop⟦m⟧)) ≫
      ((shiftFunctorOpIso C n m hnm).inv.app X)⟦m⟧' := by
  dsimp [shiftFunctorCompIsoId]
  simp only [shiftFunctorAdd'_op_hom_app X n m 0 hnm m n 0 hnm (by linarith) (add_zero 0),
    shiftFunctorZero_op_inv_app X]
  simp only [Functor.id_obj, Opposite.op_unop, Functor.op_obj, Functor.comp_obj, assoc,
    Iso.inv_hom_id_app_assoc]
  rfl

lemma opShiftFunctorEquivalence_inv_app_shift (X : Cᵒᵖ) (n m : ℤ) (hnm : n + m = 0) :
    ((opShiftFunctorEquivalence C m).unitIso.inv.app (X⟦n⟧)) =
      ((shiftFunctorCompIsoId Cᵒᵖ n m hnm).hom.app X).unop⟦m⟧'.op ≫
      ((shiftFunctorOpIso C n m hnm).inv.app X) := by
  rw [shiftFunctorCompIsoId_op_hom_app,
    opShiftFunctorEquivalence_unitIso_inv_app _ m n (by linarith)]
  simp only [opShiftFunctorEquivalence_functor, opShiftFunctorEquivalence_inverse, Functor.comp_obj, Functor.op_obj,
    Functor.id_obj, Opposite.unop_op, Opposite.op_unop, NatTrans.naturality_assoc, Functor.op_map, unop_comp,
    Quiver.Hom.unop_op, assoc, Functor.map_comp, op_comp]
  apply Quiver.Hom.unop_inj
  simp only [Opposite.op_unop, Opposite.unop_op, Quiver.Hom.unop_op, unop_comp, assoc]
  rw [shift_shiftFunctorCompIsoId_inv_app m n (by linarith) X.unop]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [← unop_comp_assoc, Iso.hom_inv_id_app, unop_id, id_comp]

variable (C)

namespace TriangleOpEquivalence

-- note that there are no signs in the definition of `functor`, but it is still
-- consistent with Verdier p. 96

@[simps]
noncomputable def functor : (Triangle C)ᵒᵖ ⥤ Triangle Cᵒᵖ where
  obj T := Triangle.mk T.unop.mor₂.op T.unop.mor₁.op
      ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.unop.obj₁) ≫
        T.unop.mor₃.op⟦(1 : ℤ)⟧')
  map {T₁ T₂} φ :=
    { hom₁ := φ.unop.hom₃.op
      hom₂ := φ.unop.hom₂.op
      hom₃ := φ.unop.hom₁.op
      comm₁ := Quiver.Hom.unop_inj φ.unop.comm₂.symm
      comm₂ := Quiver.Hom.unop_inj φ.unop.comm₁.symm
      comm₃ := by
        dsimp
        rw [assoc, ← Functor.map_comp, ← op_comp, ← φ.unop.comm₃, op_comp, Functor.map_comp]
        erw [(opShiftFunctorEquivalence C 1).counitIso.inv.naturality_assoc φ.unop.hom₁.op]
        rfl }

@[simps]
noncomputable def inverse : Triangle Cᵒᵖ ⥤ (Triangle C)ᵒᵖ where
  obj T := Opposite.op
    (Triangle.mk T.mor₂.unop T.mor₁.unop
      (((opShiftFunctorEquivalence C 1).unitIso.inv.app T.obj₁).unop ≫ T.mor₃.unop⟦(1 : ℤ)⟧'))
  map {T₁ T₂} φ := Quiver.Hom.op
    { hom₁ := φ.hom₃.unop
      hom₂ := φ.hom₂.unop
      hom₃ := φ.hom₁.unop
      comm₁ := Opposite.op_injective φ.comm₂.symm
      comm₂ := Opposite.op_injective φ.comm₁.symm
      comm₃ := by
        dsimp
        rw [assoc, ← Functor.map_comp, ← unop_comp, ← φ.comm₃, unop_comp, Functor.map_comp,
          ← unop_comp_assoc]
        apply Quiver.Hom.op_inj
        simp only [assoc, Opposite.op_unop, Quiver.Hom.op_unop, Opposite.unop_op, unop_comp, op_comp]
        erw [← (opShiftFunctorEquivalence C 1).unitIso.inv.naturality φ.hom₁]
        rfl }

@[simps!]
noncomputable def unitIso : 𝟭 _ ≅ functor C ⋙ inverse C :=
  NatIso.ofComponents (fun T => Iso.op (by
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
    · aesop_cat
    · aesop_cat
    · dsimp
      simp only [Functor.map_comp, Functor.map_id, comp_id, id_comp]
      erw [← (NatIso.unop (opShiftFunctorEquivalence C 1).unitIso).inv.naturality_assoc]
      rw [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (Opposite.op T.unop.obj₁) 1]
      dsimp
      rw [← unop_comp, Iso.hom_inv_id_app]
      dsimp
      rw [comp_id]))
    (fun {T₁ T₂} f => Quiver.Hom.unop_inj (by aesop_cat))

@[simps!]
noncomputable def counitIso : inverse C ⋙ functor C ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T => by
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
    · aesop_cat
    · aesop_cat
    · dsimp
      rw [Functor.map_id, comp_id, id_comp, Functor.map_comp]
      erw [← (opShiftFunctorEquivalence C 1).counitIso.inv.naturality_assoc T.mor₃]
      simp only [opShiftFunctorEquivalence_counitIso_inv_app_shift, ← Functor.map_comp,
        Iso.hom_inv_id_app, Functor.map_id, Functor.id_obj, comp_id, Functor.id_map])
    (by aesop_cat)

end TriangleOpEquivalence

@[simps]
noncomputable def triangleOpEquivalence :
    (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ where
  functor := TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

variable [HasZeroObject C] [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C]

namespace Opposite

def distinguishedTriangles : Set (Triangle Cᵒᵖ) :=
  fun T => ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C

variable {C}

lemma mem_distinguishedOp_iff (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔ ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C :=
  by rfl

lemma mem_distinguishedOp_iff' (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
      Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) := by
  rw [mem_distinguishedOp_iff]
  constructor
  · intro hT
    exact ⟨_ ,hT, ⟨(triangleOpEquivalence C).counitIso.symm.app T⟩⟩
  · rintro ⟨T', hT', ⟨e⟩⟩
    refine' isomorphic_distinguished _ hT' _ _
    exact Iso.unop ((triangleOpEquivalence C).unitIso.app (Opposite.op T') ≪≫
      (triangleOpEquivalence C).inverse.mapIso e.symm)

lemma isomorphic_distinguished (T₁ : Triangle Cᵒᵖ)
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle Cᵒᵖ)
    (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedOp_iff] at hT₁ ⊢
  exact Pretriangulated.isomorphic_distinguished _ hT₁ _
    ((triangleOpEquivalence C).inverse.mapIso e).unop.symm

noncomputable def contractibleTriangleIso (X : Cᵒᵖ) :
    contractibleTriangle X ≅ (triangleOpEquivalence C).functor.obj
      (Opposite.op (contractibleTriangle X.unop).invRotate) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    { hom := 0
      inv := 0
      inv_hom_id := IsZero.eq_of_tgt (by
        rw [IsZero.iff_id_eq_zero]
        change (𝟙 ((0 : C)⟦(-1 : ℤ)⟧)).op = 0
        rw [← Functor.map_id, id_zero, Functor.map_zero, op_zero]) _ _ }
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

lemma contractible_distinguished (X : Cᵒᵖ) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  rw [mem_distinguishedOp_iff']
  exact ⟨_, inv_rot_of_dist_triangle _ (Pretriangulated.contractible_distinguished X.unop),
    ⟨contractibleTriangleIso X⟩⟩

noncomputable def rotateTriangleOpEquivalenceInverseObjRotateUnop
    (T : Triangle Cᵒᵖ) :
    Triangle.rotate ((triangleOpEquivalence C).inverse.obj (Triangle.rotate T)).unop ≅
      ((triangleOpEquivalence C).inverse.obj T).unop := by
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (mulIso (-1) ((opShiftFunctorEquivalence C 1).unitIso.app T.obj₁).unop) _ _ _
  · dsimp
    simp
  · dsimp
    rw [neg_smul, one_smul, comp_neg]
    rw [id_comp]
    erw [Functor.map_neg]
    dsimp
    rw [comp_neg, neg_comp, neg_neg]
    apply Quiver.Hom.op_inj
    simp only [op_comp, assoc]
    erw [(opShiftFunctorEquivalence C 1).unitIso.inv.naturality T.mor₁]
    dsimp
    rw [Iso.hom_inv_id_app_assoc]
  · dsimp
    simp only [Functor.map_id, comp_id, neg_smul, one_smul, neg_comp, neg_inj,
       ← assoc, ← unop_comp, Iso.inv_hom_id_app, Functor.comp_obj, unop_id,
       Opposite.unop_op, Functor.op_obj, id_comp]

lemma rotate_distinguished_triangle (T : Triangle Cᵒᵖ) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  simp only [mem_distinguishedOp_iff, Pretriangulated.rotate_distinguished_triangle
    ((triangleOpEquivalence C).inverse.obj (T.rotate)).unop]
  exact distinguished_iff_of_iso (rotateTriangleOpEquivalenceInverseObjRotateUnop T).symm

lemma distinguished_cocone_triangle {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ∃ (Z : Cᵒᵖ) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨Z, g, h, H⟩ := Pretriangulated.distinguished_cocone_triangle₁ f.unop
  simp only [mem_distinguishedOp_iff]
  refine' ⟨_, g.op, (opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op Z) ≫
    (shiftFunctor Cᵒᵖ (1 : ℤ)).map h.op, _⟩
  dsimp
  convert H using 2
  dsimp
  rw [Functor.map_comp]
  apply Quiver.Hom.op_inj
  rw [op_comp, op_comp, shift_unop_opShiftFunctorEquivalence_counitIso_inv_app (Opposite.op Z) 1]
  erw [← (opShiftFunctorEquivalence C 1).unitIso.hom.naturality h.op,
    assoc, Iso.hom_inv_id_app, comp_id]
  rfl

lemma complete_distinguished_triangle_morphism (T₁ T₂ : Triangle Cᵒᵖ)
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦1⟧' = c ≫ T₂.mor₃ := by
  rw [mem_distinguishedOp_iff] at hT₁ hT₂
  obtain ⟨c, hc₁, hc₂⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hT₂ hT₁ b.unop
    a.unop (Quiver.Hom.op_inj comm.symm)
  dsimp at c hc₁ hc₂
  simp only [neg_comp, assoc, comp_neg, neg_inj] at hc₂
  refine' ⟨c.op, Quiver.Hom.unop_inj hc₁.symm, Quiver.Hom.unop_inj _⟩
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [unop_comp, unop_comp, Functor.map_comp, Functor.map_comp, Quiver.Hom.unop_op,
      ← cancel_epi ((opShiftFunctorEquivalence C 1).unitIso.inv.app T₂.obj₁).unop, hc₂]
  apply Quiver.Hom.op_inj
  simp only [op_comp, Functor.id_obj, Opposite.op_unop, Functor.comp_obj, Functor.op_obj,
    Opposite.unop_op, Quiver.Hom.op_unop, assoc]
  congr 1
  exact (opShiftFunctorEquivalence C 1).unitIso.inv.naturality a

scoped instance : Pretriangulated Cᵒᵖ where
  distinguishedTriangles := distinguishedTriangles C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

end Opposite

variable {C}

lemma mem_distTriang_op_iff (T : Triangle Cᵒᵖ) :
    (T ∈ distTriang Cᵒᵖ) ↔ ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C := by
  rfl

lemma mem_distTriang_op_iff' (T : Triangle Cᵒᵖ) :
    (T ∈ distTriang Cᵒᵖ) ↔ ∃ (T' : Triangle C) (_ : T' ∈ distTriang C),
      Nonempty (T ≅ (triangleOpEquivalence C).functor.obj (Opposite.op T')) :=
  Opposite.mem_distinguishedOp_iff' T

lemma op_distinguished (T : Triangle C) (hT : T ∈ distTriang C) :
    ((triangleOpEquivalence C).functor.obj (Opposite.op T)) ∈ distTriang Cᵒᵖ := by
  rw [mem_distTriang_op_iff']
  exact ⟨T, hT, ⟨Iso.refl _⟩⟩

lemma unop_distinguished (T : Triangle Cᵒᵖ) (hT : T ∈ distTriang Cᵒᵖ) :
    ((triangleOpEquivalence C).inverse.obj T).unop ∈ distTriang C := hT

namespace Opposite

/-scoped instance [IsTriangulated C] : IsTriangulated Cᵒᵖ where
  octahedron_axiom := by
    intro X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
    have h₁₂' := (unop_distinguished _ (inv_rot_of_dist_triangle _ h₂₃))
    have h₂₃' := (unop_distinguished _ (inv_rot_of_dist_triangle _ h₁₂))
    have h₁₃' := (unop_distinguished _ (inv_rot_of_dist_triangle _ h₁₃))
    have comm' : u₂₃.unop ≫ u₁₂.unop = u₁₃.unop := by rw [← unop_comp, comm]
    have H := Triangulated.someOctahedron comm' h₁₂' h₂₃' h₁₃'
    obtain ⟨m₁, hm₁⟩ : ∃ (m₁ : Z₁₂ ⟶ Z₁₃), m₁⟦(-1 : ℤ)⟧' = H.m₃.op :=
      ⟨(shiftFunctor Cᵒᵖ (-1 : ℤ)).preimage H.m₃.op, by simp⟩
    obtain ⟨m₃, hm₃⟩ : ∃ (m₃ : Z₁₃ ⟶ Z₂₃), m₃⟦(-1 : ℤ)⟧' = H.m₁.op :=
      ⟨(shiftFunctor Cᵒᵖ (-1 : ℤ)).preimage H.m₁.op, by simp⟩
    refine' ⟨
      { m₁ := m₁
        m₃ := m₃
        comm₁ := (shiftFunctor Cᵒᵖ (-1 : ℤ)).map_injective (by
          -- draft...
          have eq := congr_arg Quiver.Hom.op H.comm₄
          dsimp at eq
          simp at eq
          simp only [opShiftFunctorEquivalence_inv_app_shift _ _ _ (neg_add_self 1)] at eq
          simp only [← op_comp_assoc, assoc, ← Functor.map_comp_assoc, ← unop_comp_assoc,
            Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, ← unop_comp] at eq
          simp at eq
          simp only [Functor.map_comp, hm₁, shiftFunctor_op_map (-1) 1 (neg_add_self 1),
            Functor.op_obj, unop_comp, Functor.map_comp, op_comp, assoc, NatIso.cancel_natIso_hom_left]
          rw [eq]
          congr 1
          rw [← hm₁]
          exact (shiftFunctorOpIso C _ _ (neg_add_self 1)).inv.naturality m₁ )
        comm₂ := sorry
        comm₃ := sorry
        comm₄ := sorry
        mem := by
          rw [← Triangle.shift_distinguished_iff _ (-1), mem_distTriang_op_iff']
          refine' ⟨_, H.mem, ⟨_⟩⟩
          refine' Triangle.isoMk _ _ (Iso.refl _) (mulIso (-1) (Iso.refl _)) (Iso.refl _) _ _ _
          · aesop_cat
          · aesop_cat
          · dsimp
            simp only [Int.negOnePow_neg, Int.negOnePow_one, Functor.map_comp, assoc, neg_smul, one_smul,
              Functor.map_id, comp_id, Functor.map_neg, op_neg, op_comp, neg_comp, comp_neg, id_comp, neg_inj]
            sorry
          } ⟩ -/

end Opposite

end Pretriangulated

end CategoryTheory
