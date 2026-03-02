/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Kähler differential module under base change

## Main results
- `KaehlerDifferential.tensorKaehlerEquivBase`: `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.tensorKaehlerEquiv`: `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`:
  `Ω[Aₚ/Rₚ]` is the localization of `Ω[A/R]` at `p`.

-/

@[expose] public section

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

open TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local irreducible] KaehlerDifferential

namespace KaehlerDifferential

/-- (Implementation). `A`-action on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
abbrev mulActionBaseChange : MulAction A (S ⊗[R] Ω[A⁄R]) :=
  (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A

attribute [local instance] mulActionBaseChange

@[simp]
lemma mulActionBaseChange_smul_tmul (a : A) (s : S) (x : Ω[A⁄R]) :
    a • (s ⊗ₜ[R] x) = s ⊗ₜ (a • x) := rfl

@[local simp]
lemma mulActionBaseChange_smul_zero (a : A) :
    a • (0 : S ⊗[R] Ω[A⁄R]) = 0 := by
  rw [← zero_tmul _ (0 : Ω[A⁄R]), mulActionBaseChange_smul_tmul, smul_zero]

@[local simp]
lemma mulActionBaseChange_smul_add (a : A) (x y : S ⊗[R] Ω[A⁄R]) :
    a • (x + y) = a • x + a • y := by
  change (TensorProduct.comm R S Ω[A⁄R]).symm (a • (TensorProduct.comm R S Ω[A⁄R]) (x + y)) = _
  rw [map_add, smul_add, map_add]
  rfl

/-- (Implementation). `A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
abbrev moduleBaseChange :
    Module A (S ⊗[R] Ω[A⁄R]) where
  __ := (TensorProduct.comm R S Ω[A⁄R]).toEquiv.mulAction A
  add_smul r s x := by induction x <;> simp [add_smul, tmul_add, *, add_add_add_comm]
  zero_smul x := by induction x <;> simp [*]
  smul_zero := by simp
  smul_add := by simp

attribute [local instance] moduleBaseChange

instance : IsScalarTower R A (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x
  · simp only [smul_zero]
  · rw [mulActionBaseChange_smul_tmul, algebraMap_smul, tmul_smul]
  · simp only [smul_add, *]

instance : SMulCommClass S A (S ⊗[R] Ω[A⁄R]) where
  smul_comm s a x := by
    induction x
    · simp only [smul_zero]
    · rw [mulActionBaseChange_smul_tmul, smul_tmul', smul_tmul', mulActionBaseChange_smul_tmul]
    · simp only [smul_add, *]

instance : SMulCommClass A S (S ⊗[R] Ω[A⁄R]) where
  smul_comm s a x := by rw [← smul_comm]

/-- (Implementation). `B = S ⊗[R] A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
@[reducible] noncomputable
def moduleBaseChange' [Algebra.IsPushout R S A B] :
    Module B (S ⊗[R] Ω[A⁄R]) :=
  Module.compHom _ (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)).toRingHom

attribute [local instance] moduleBaseChange'

instance [Algebra.IsPushout R S A B] :
    IsScalarTower A B (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap A B r)) • x = r • x
  simp only [Algebra.pushoutDesc_right, Module.End.smul_def, Algebra.lsmul_coe]

instance [Algebra.IsPushout R S A B] :
    IsScalarTower S B (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  change (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap S B r)) • x = r • x
  simp only [Algebra.pushoutDesc_left, Module.End.smul_def, Algebra.lsmul_coe]

lemma map_liftBaseChange_smul [h : Algebra.IsPushout R S A B] (b : B) (x) :
    ((map R S A B).restrictScalars R).liftBaseChange S (b • x) =
    b • ((map R S A B).restrictScalars R).liftBaseChange S x := by
  induction b using h.1.inductionOn with
  | zero => simp only [zero_smul, map_zero]
  | smul s b e => rw [smul_assoc, map_smul, e, smul_assoc]
  | add b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂, add_smul]
  | tmul a =>
    induction x
    · simp only [smul_zero, map_zero]
    · simp [smul_comm]
    · simp only [map_add, smul_add, *]

/-- (Implementation).
The `S`-derivation `B = S ⊗[R] A` to `S ⊗[R] Ω[A⁄R]` sending `a ⊗ b` to `a ⊗ d b`. -/
noncomputable
def derivationTensorProduct [h : Algebra.IsPushout R S A B] :
    Derivation S B (S ⊗[R] Ω[A⁄R]) where
  __ := h.out.lift ((TensorProduct.mk R S Ω[A⁄R] 1).comp (D R A).toLinearMap)
  map_one_eq_zero' := by
    rw [← (algebraMap A B).map_one]
    refine (h.out.lift_eq _ _).trans ?_
    dsimp
    rw [Derivation.map_one_eq_zero, TensorProduct.tmul_zero]
  leibniz' a b := by
    induction a using h.out.inductionOn with
    | zero => rw [map_zero, zero_smul, smul_zero, zero_add, zero_mul, map_zero]
    | smul x y e =>
      rw [smul_mul_assoc, map_smul, e, map_smul, smul_add,
        smul_comm x b, smul_assoc]
    | add b₁ b₂ e₁ e₂ => simp only [add_mul, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
    | tmul z =>
      dsimp
      induction b using h.out.inductionOn with
      | zero => rw [map_zero, zero_smul, smul_zero, zero_add, mul_zero, map_zero]
      | tmul =>
        simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          algebraMap_smul, ← map_mul]
        rw [← IsScalarTower.toAlgHom_apply R, ← AlgHom.toLinearMap_apply, h.out.lift_eq,
          ← IsScalarTower.toAlgHom_apply R, ← AlgHom.toLinearMap_apply, h.out.lift_eq,
          ← IsScalarTower.toAlgHom_apply R, ← AlgHom.toLinearMap_apply, h.out.lift_eq]
        simp only [LinearMap.coe_comp, Derivation.coeFn_coe, Function.comp_apply,
          Derivation.leibniz, mk_apply, mulActionBaseChange_smul_tmul, TensorProduct.tmul_add]
      | smul _ _ e =>
        rw [mul_comm, smul_mul_assoc, map_smul, mul_comm, e,
            map_smul, smul_add, smul_comm, smul_assoc]
      | add _ _ e₁ e₂ => simp only [mul_add, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]

lemma derivationTensorProduct_algebraMap [Algebra.IsPushout R S A B] (x) :
    derivationTensorProduct R S A B (algebraMap A B x) =
    1 ⊗ₜ D _ _ x :=
IsBaseChange.lift_eq _ _ _

lemma tensorKaehlerEquiv_left_inv [Algebra.IsPushout R S A B] :
    ((derivationTensorProduct R S A B).liftKaehlerDifferential.restrictScalars S).comp
    (((map R S A B).restrictScalars R).liftBaseChange S) = LinearMap.id := by
  refine LinearMap.restrictScalars_injective R ?_
  apply TensorProduct.ext'
  intro x y
  obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
  induction y
  · simp only [map_zero, TensorProduct.tmul_zero]
  · simp only [LinearMap.restrictScalars_comp, Derivation.tensorProductTo_tmul, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.liftBaseChange_tmul, map_smul,
      map_D, LinearMap.map_smul_of_tower, Derivation.liftKaehlerDifferential_comp_D,
      LinearMap.id_coe, id_eq, derivationTensorProduct_algebraMap]
    rw [smul_comm, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  · simp only [map_add, TensorProduct.tmul_add, *]

/-- The canonical isomorphism `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquiv` for the version with `B ⊗[A] Ω[A⁄R]`. -/
@[simps! symm_apply] noncomputable
def tensorKaehlerEquivBase [h : Algebra.IsPushout R S A B] :
    (S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S] where
  __ := ((map R S A B).restrictScalars R).liftBaseChange S
  invFun := (derivationTensorProduct R S A B).liftKaehlerDifferential
  left_inv := LinearMap.congr_fun (tensorKaehlerEquiv_left_inv R S A B)
  right_inv x := by
    obtain ⟨x, rfl⟩ := tensorProductTo_surjective _ _ x
    dsimp
    induction x with
    | zero => simp
    | add x y e₁ e₂ => simp only [map_add, e₁, e₂]
    | tmul x y =>
      dsimp
      -- We use the specialized version of `map_smul` here for performance.
      simp only [Derivation.tensorProductTo_tmul, LinearMap.map_smul,
        Derivation.liftKaehlerDifferential_comp_D, map_liftBaseChange_smul]
      induction y using h.1.inductionOn
      · simp only [map_zero, smul_zero]
      · simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          derivationTensorProduct_algebraMap, LinearMap.liftBaseChange_tmul,
          LinearMap.coe_restrictScalars, map_D, one_smul]
      · -- We use the specialized version of `map_smul` here for performance.
        simp only [Derivation.map_smul, LinearMap.map_smul, *, smul_comm x]
      · simp only [map_add, smul_add, *]

@[simp]
lemma tensorKaehlerEquivBase_tmul [Algebra.IsPushout R S A B] (a b) :
    tensorKaehlerEquivBase R S A B (a ⊗ₜ b) = a • map R S A B b :=
  LinearMap.liftBaseChange_tmul _ _ _ _

@[deprecated (since := "2026-01-01")] alias tensorKaehlerEquiv_tmul := tensorKaehlerEquivBase_tmul

/--
If `B` is the tensor product of `S` and `A` over `R`,
then `Ω[B⁄S]` is the base change of `Ω[A⁄R]` along `R → S`.
-/
lemma isBaseChange [h : Algebra.IsPushout R S A B] :
    IsBaseChange S ((map R S A B).restrictScalars R) := by
  convert (TensorProduct.isBaseChange R Ω[A⁄R] S).comp
    (IsBaseChange.ofEquiv (tensorKaehlerEquivBase R S A B))
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, mk_apply, tensorKaehlerEquivBase_tmul, one_smul]

instance isLocalizedModule (p : Submonoid R) [IsLocalization p S]
      [IsLocalization (Algebra.algebraMapSubmonoid A p) B] :
    IsLocalizedModule p ((map R S A B).restrictScalars R) :=
  have := (Algebra.isPushout_of_isLocalization p S A B).symm
  (isLocalizedModule_iff_isBaseChange p S _).mpr (isBaseChange R S A B)

instance isLocalizedModule_of_isLocalizedModule (p : Submonoid R) [IsLocalization p S]
      [IsLocalizedModule p (IsScalarTower.toAlgHom R A B).toLinearMap] :
    IsLocalizedModule p ((map R S A B).restrictScalars R) :=
  have : IsLocalization (Algebra.algebraMapSubmonoid A p) B :=
    isLocalizedModule_iff_isLocalization.mp inferInstance
  inferInstance

/-- The canonical isomorphism `(B ⊗[A] Ω[A⁄R]) ≃ₗ[B] Ω[B⁄S]` for `B = S ⊗[R] A`.
Also see `KaehlerDifferential.tensorKaehlerEquivBase` for the version with `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
def tensorKaehlerEquiv [h : Algebra.IsPushout R S A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B ⊗[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] ⊗[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv (.refl _ _)
      ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B ⊗[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquivBase R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *]
  | tmul x y =>
  obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
  | tmul x z =>
  suffices b • z • a • x • KaehlerDifferential.map R S A B y =
      (algebraMap A B a * algebraMap S B b) • z • x • KaehlerDifferential.map R S A B y by
    simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
      Algebra.IsPushout.equiv_symm_algebraMap_left, Algebra.IsPushout.equiv_symm_algebraMap_right]
  simp only [← mul_smul, ← @algebraMap_smul S _ B, ← @algebraMap_smul A _ B]
  ring_nf

@[simp]
lemma tensorKaehlerEquiv_tmul_D [Algebra.IsPushout R S A B] (b a) :
    tensorKaehlerEquiv R S A B (b ⊗ₜ D _ _ a) = b • D S B (algebraMap A B a) := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
  trans s • a' • D S B (algebraMap A B a)
  · simp [tensorKaehlerEquiv]
  · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma tensorKaehlerEquiv_symm_D_tmul (s a) :
    (tensorKaehlerEquiv R S A (S ⊗[R] A)).symm (D _ _ (s ⊗ₜ a)) = algebraMap _ _ s ⊗ₜ D _ _ a := by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [show s ⊗ₜ 1 = algebraMap S (S ⊗ A) s by simp, Algebra.TensorProduct.right_algebraMap_apply,
    algebraMap_smul, ← Derivation.map_smul, smul_tmul', smul_eq_mul, mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma tensorKaehlerEquiv_symm_D_tmul' (s a) :
    (tensorKaehlerEquiv R S A (A ⊗[R] S)).symm (D _ _ (a ⊗ₜ s)) = algebraMap _ _ s ⊗ₜ D _ _ a := by
  apply (tensorKaehlerEquiv R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv_tmul_D]
  rw [algebraMap_smul, ← Derivation.map_smul, Algebra.smul_def,
    Algebra.TensorProduct.right_algebraMap_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end KaehlerDifferential
