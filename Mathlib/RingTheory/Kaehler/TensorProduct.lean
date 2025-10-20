/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Kähler differential module under base change

## Main results
- `KaehlerDifferential.tensorKaehlerEquiv`: `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`:
  `Ω[Aₚ/Rₚ]` is the localization of `Ω[A/R]` at `p`.

-/

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

open TensorProduct

attribute [local instance] SMulCommClass.of_commMonoid

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
  rw [map_add, smul_add, (TensorProduct.comm R S Ω[A⁄R]).symm.map_add]
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

/-- The canonical isomorphism `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`. -/
@[simps! symm_apply] noncomputable
def tensorKaehlerEquiv [h : Algebra.IsPushout R S A B] :
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
      simp only [Derivation.tensorProductTo_tmul, LinearMap.map_smul,
        Derivation.liftKaehlerDifferential_comp_D, map_liftBaseChange_smul]
      induction y using h.1.inductionOn
      · simp only [map_zero, smul_zero]
      · simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          derivationTensorProduct_algebraMap, LinearMap.liftBaseChange_tmul,
          LinearMap.coe_restrictScalars, map_D, one_smul]
      · simp only [Derivation.map_smul, LinearMap.map_smul, *, smul_comm x]
      · simp only [map_add, smul_add, *]

@[simp]
lemma tensorKaehlerEquiv_tmul [Algebra.IsPushout R S A B] (a b) :
    tensorKaehlerEquiv R S A B (a ⊗ₜ b) = a • map R S A B b :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/--
If `B` is the tensor product of `S` and `A` over `R`,
then `Ω[B⁄S]` is the base change of `Ω[A⁄R]` along `R → S`.
-/
lemma isBaseChange [h : Algebra.IsPushout R S A B] :
    IsBaseChange S ((map R S A B).restrictScalars R) := by
  convert (TensorProduct.isBaseChange R Ω[A⁄R] S).comp
    (IsBaseChange.ofEquiv (tensorKaehlerEquiv R S A B))
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, mk_apply, tensorKaehlerEquiv_tmul, one_smul]

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

end KaehlerDifferential
