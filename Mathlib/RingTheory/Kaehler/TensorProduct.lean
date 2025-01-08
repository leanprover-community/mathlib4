/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Kaehler.CotangentComplex
import Mathlib.RingTheory.Flat.Equalizer

/-!
# Kaehler differential module under base change

## Main results
- `KaehlerDifferential.tensorKaehlerEquiv`: `(S ⊗[R] Ω[A⁄R]) ≃ₗ[S] Ω[B⁄S]` for `B = S ⊗[R] A`.
- `KaehlerDifferential.isLocalizedModule_of_isLocalizedModule`:
  `Ω[Aₚ/Rₚ]` is the localization of `Ω[A/R]` at `p`.

-/

variable (R S A B : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable [Algebra A B] [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B]

open TensorProduct

@[reducible]
noncomputable
def TensorProduct.rightModule
    {R : Type*} [CommSemiring R] {R'' : Type*} [Semiring R''] {M : Type*} {N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module R'' N]
    [SMulCommClass R'' R N] : Module R'' (M ⊗[R] N) where
  smul r := (Module.toModuleEnd R N r).lTensor M
  one_smul x := show (Module.toModuleEnd R N 1).lTensor M x = x by
    rw [map_one, LinearMap.one_eq_id, LinearMap.lTensor_id, LinearMap.id_apply]
  mul_smul x y a := show (Module.toModuleEnd R N (x * y)).lTensor M a = _ by
    rw [map_mul, LinearMap.mul_eq_comp, LinearMap.lTensor_comp]; rfl
  smul_zero r := ((Module.toModuleEnd R N r).lTensor M).map_zero
  smul_add r := ((Module.toModuleEnd R N r).lTensor M).map_add
  add_smul x y a := show (Module.toModuleEnd R N (x + y)).lTensor M a = _ by
    rw [map_add, LinearMap.lTensor_add]; rfl
  zero_smul a := show (Module.toModuleEnd R N 0).lTensor M a = _ by
    rw [map_zero, LinearMap.lTensor_zero]; rfl

attribute [local instance] TensorProduct.rightModule in
lemma TensorProduct.isScalarTower_rightModule
    {R : Type*} [CommSemiring R] {R'' : Type*} [Semiring R''] {M : Type*} {N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] [Module R'' N]
    [Algebra R R''] [IsScalarTower R R'' N] : IsScalarTower R R'' (M ⊗[R] N) :=
  .of_algebraMap_smul fun r m ↦
  show (Algebra.lsmul R _ _ (algebraMap _ _ _)).lTensor _ m = r • m by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, LinearMap.lTensor_smul,
    LinearMap.one_eq_id, LinearMap.lTensor_id, @LinearMap.smul_apply, @LinearMap.id_apply]

attribute [local instance] SMulCommClass.of_commMonoid

namespace KaehlerDifferential

/-- (Implementation). `A`-module structure on `S ⊗[R] Ω[A⁄R]`. -/
noncomputable
abbrev moduleBaseChange :
    Module A (S ⊗[R] Ω[A⁄R]) := TensorProduct.rightModule

attribute [local instance] moduleBaseChange

@[simp]
lemma mulActionBaseChange_smul_tmul (a : A) (s : S) (x : Ω[A⁄R]) :
    a • (s ⊗ₜ[R] x) = s ⊗ₜ (a • x) := rfl

instance : IsScalarTower R A (S ⊗[R] Ω[A⁄R]) := TensorProduct.isScalarTower_rightModule

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
  show (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap A B r)) • x = r • x
  simp only [Algebra.pushoutDesc_right, LinearMap.smul_def, Algebra.lsmul_coe]

instance [Algebra.IsPushout R S A B] :
    IsScalarTower S B (S ⊗[R] Ω[A⁄R]) := by
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  show (Algebra.pushoutDesc B (Algebra.lsmul R (A := S) S (S ⊗[R] Ω[A⁄R]))
    (Algebra.lsmul R (A := A) _ _) (LinearMap.ext <| smul_comm · ·)
      (algebraMap S B r)) • x = r • x
  simp only [Algebra.pushoutDesc_left, LinearMap.smul_def, Algebra.lsmul_coe]

lemma map_liftBaseChange_smul [h : Algebra.IsPushout R S A B] (b : B) (x) :
    ((map R S A B).restrictScalars R).liftBaseChange S (b • x) =
    b • ((map R S A B).restrictScalars R).liftBaseChange S x := by
  induction b using h.1.inductionOn with
  | h₁ => simp only [zero_smul, map_zero]
  | h₃ s b e => rw [smul_assoc, map_smul, e, smul_assoc]
  | h₄ b₁ b₂ e₁ e₂ => simp only [map_add, e₁, e₂, add_smul]
  | h₂ a =>
    induction x
    · simp only [smul_zero, map_zero]
    · simp [smul_comm]
    · simp only [map_add, smul_add, *]

/-- (Implementation).
The `S`-derivation `B = S ⊗[R] A` to `S ⊗[R] Ω[A⁄R]` sending `a ⊗ b` to `a ⊗ d b`. -/
noncomputable
def derivationTensorProduct [h : Algebra.IsPushout R S A B] :
    Derivation S B (S ⊗[R] Ω[A⁄R]) where
  __ := h.out.lift ((TensorProduct.mk R S (Ω[A⁄R]) 1).comp (D R A).toLinearMap)
  map_one_eq_zero' := by
    rw [← (algebraMap A B).map_one]
    refine (h.out.lift_eq _ _).trans ?_
    dsimp
    rw [Derivation.map_one_eq_zero, TensorProduct.tmul_zero]
  leibniz' a b := by
    dsimp
    induction a using h.out.inductionOn with
    | h₁ => rw [map_zero, zero_smul, smul_zero, zero_add, zero_mul, map_zero]
    | h₃ x y e =>
      rw [smul_mul_assoc, map_smul, e, map_smul, smul_add,
        smul_comm x b, smul_assoc]
    | h₄ b₁ b₂ e₁ e₂ => simp only [add_mul, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]
    | h₂ z =>
      dsimp
      induction b using h.out.inductionOn with
      | h₁ => rw [map_zero, zero_smul, smul_zero, zero_add, mul_zero, map_zero]
      | h₂ =>
        simp only [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
          algebraMap_smul, ← map_mul]
        erw [h.out.lift_eq, h.out.lift_eq, h.out.lift_eq]
        simp only [LinearMap.coe_comp, Derivation.coeFn_coe, Function.comp_apply,
          Derivation.leibniz, mk_apply, mulActionBaseChange_smul_tmul, TensorProduct.tmul_add]
      | h₃ _ _ e =>
        rw [mul_comm, smul_mul_assoc, map_smul, mul_comm, e,
            map_smul, smul_add, smul_comm, smul_assoc]
      | h₄ _ _ e₁ e₂ => simp only [mul_add, add_smul, map_add, e₁, e₂, smul_add, add_add_add_comm]

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
  convert (TensorProduct.isBaseChange R (Ω[A⁄R]) S).comp
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

namespace Algebra

attribute [local instance] SMulCommClass.of_commMonoid

universe u

variable {R S}
variable (P : Extension.{u} R S) (T : Type*) [CommRing T] [Algebra R T]

open scoped TensorProduct

open KaehlerDifferential

attribute [local instance] TensorProduct.rightAlgebra in
noncomputable
instance : Module S (P.tensorAlgebra T).CotangentSpace := TensorProduct.leftModule

attribute [local instance] TensorProduct.rightAlgebra in
instance : IsScalarTower R S (P.tensorAlgebra T).CotangentSpace := inferInstance

noncomputable
instance : Module T (P.tensorAlgebra T).CotangentSpace := TensorProduct.leftModule

noncomputable
instance : Module (T ⊗[R] S) (T ⊗[R] P.CotangentSpace) :=
  letI : Module S (T ⊗[R] P.CotangentSpace) := TensorProduct.rightModule
  have : IsScalarTower R S (T ⊗[R] P.CotangentSpace) := TensorProduct.isScalarTower_rightModule
  have : SMulCommClass S R (T ⊗[R] P.CotangentSpace) := IsScalarTower.to_smulCommClass'
  letI f : T ⊗[R] S →ₐ[R] Module.End R (T ⊗[R] P.CotangentSpace) :=
    Algebra.TensorProduct.lift (Algebra.lsmul _ _ _) (Algebra.lsmul _ _ _) fun a b ↦ by ext; rfl
  Module.compHom _ f.toRingHom

noncomputable
instance : Module (P.tensorAlgebra T).Ring (T ⊗[R] P.CotangentSpace) :=
  Module.compHom _ (algebraMap (P.tensorAlgebra T).Ring (T ⊗[R] S))

instance : IsScalarTower (P.tensorAlgebra T).Ring (T ⊗[R] S) (T ⊗[R] P.CotangentSpace) :=
  .of_algebraMap_smul fun _ _ ↦ rfl

instance : IsScalarTower T (T ⊗[R] S) (T ⊗[R] P.CotangentSpace) :=
  .of_algebraMap_smul fun r m ↦ by
    letI : Module S (T ⊗[R] P.CotangentSpace) := TensorProduct.rightModule
    show r • ((1 : S) • m) = _
    rw [one_smul]

instance : IsScalarTower R (T ⊗[R] S) (T ⊗[R] P.CotangentSpace) :=
  .of_algebraMap_smul fun r m ↦ by
    rw [IsScalarTower.algebraMap_apply R T, algebraMap_smul, algebraMap_smul]

attribute [local instance] TensorProduct.rightAlgebra in
/-- Given an `R`-extension `0 → I → P → S → 0` and a `R`-algebra `T`,
this is the caononical map `Ω[T ⊗ P/R] → T ⊗ (S ⊗[P] Ω[P/R])`.
This map exhibits `T ⊗ (S ⊗[P] Ω[P/R])` as the base change of `Ω[T ⊗ P/R]` to `T ⊗ S`.
See `cotangentSpaceTensorAlgebraEquiv`. -/
noncomputable
def Extension.cotangentSpaceTensorAlgebraAux :
    Ω[(P.tensorAlgebra T).Ring⁄R] →ₗ[T] T ⊗[R] P.CotangentSpace :=
  ((TensorProduct.mk P.Ring S (Ω[P.Ring⁄R]) 1).restrictScalars R).baseChange T ∘ₗ
    (KaehlerDifferential.tensorKaehlerEquiv
      R T P.Ring (T ⊗[R] P.Ring)).symm.toLinearMap ∘ₗ
    (KaehlerDifferential.map R T (T ⊗[R] P.Ring) (T ⊗[R] P.Ring)).restrictScalars T

attribute [local instance] TensorProduct.rightAlgebra
  KaehlerDifferential.moduleBaseChange
  KaehlerDifferential.moduleBaseChange' in
lemma Extension.cotangentSpaceTensorAlgebraAux_apply_smul_D
    (a b : T) (c d : P.Ring) :
    P.cotangentSpaceTensorAlgebraAux T (((by exact a ⊗ₜ[R] c) :
      (P.tensorAlgebra T).Ring) • .D _ _ (b ⊗ₜ d)) = (a * b) ⊗ₜ (1 ⊗ₜ (c • D _ _ d)) := by
  have H : derivationTensorProduct R T P.Ring (T ⊗[R] P.Ring) (b ⊗ₜ[R] d) = b ⊗ₜ .D _ _ d := by
    trans b • 1 ⊗ₜ .D _ _ d
    · rw [← derivationTensorProduct_algebraMap R T _ (T ⊗[R] P.Ring), ← Derivation.map_smul]
      congr 1
      show _ = b • 1 ⊗ₜ d
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have : algebraMap _ _ a * algebraMap _ _ c = a ⊗ₜ[R] c :=
    (TensorProduct.tmul_mul_tmul _ _ _ _).trans (by simp)
  dsimp [tensorAlgebra, ofSurjective, cotangentSpaceTensorAlgebraAux]
  simp only [LinearMap.map_smul, map_D, id.map_eq_id, RingHom.id_apply,
    Derivation.liftKaehlerDifferential_comp_D, H]
  rw [← this, mul_smul, algebraMap_smul, algebraMap_smul]
  rfl

lemma Extension.cotangentSpaceTensorAlgebraAux_apply_D
    (b : T) (d : P.Ring) :
    P.cotangentSpaceTensorAlgebraAux T (D _ _ (b ⊗ₜ d)) = b ⊗ₜ (1 ⊗ₜ D _ _ d) := by
  simpa [← TensorProduct.one_def] using
    P.cotangentSpaceTensorAlgebraAux_apply_smul_D T 1 b 1 d

set_option maxHeartbeats 400000 in
lemma Extension.cotangentSpaceTensorAlgebraAux_smul
    (r : (P.tensorAlgebra T).Ring) (x : Ω[(P.tensorAlgebra T).Ring⁄R]) :
    P.cotangentSpaceTensorAlgebraAux T (r • x) = r • P.cotangentSpaceTensorAlgebraAux T x := by
  obtain ⟨x, rfl⟩ := tensorProductTo_surjective _ _ x
  induction x with
  | zero => simp only [map_zero, smul_zero]
  | add x y _ _ => simp only [map_add, smul_add, *]
  | tmul x y =>
    simp only [Derivation.tensorProductTo_tmul]
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero]
    | add a b _ _ => simp only [map_add, smul_add, *]
    | tmul y z =>
      induction x using TensorProduct.induction_on with
      | zero => simp only [zero_smul, smul_zero, map_zero]
      | add x y hx hy =>
        simp only [tensorAlgebra, ofSurjective, AlgHom.toRingHom_eq_coe,
          add_smul, map_add, smul_add] at hx hy ⊢
        rw [hx, hy, smul_add (A := T ⊗[R] P.CotangentSpace) r]
      | tmul a b =>
        induction r using TensorProduct.induction_on with
        | zero => simp only [zero_smul, smul_zero, map_zero]
        | add x y hx hy => simp only [add_smul, map_add, hx, hy]
        | tmul s t =>
          rw [← mul_smul, TensorProduct.tmul_mul_tmul,
            Extension.cotangentSpaceTensorAlgebraAux_apply_smul_D,
            Extension.cotangentSpaceTensorAlgebraAux_apply_smul_D,
            mul_assoc, mul_smul, tmul_smul t, ← algebraMap_smul S t]
          rfl

/-- Given an `R`-extension `0 → I → P → S → 0` and a formally unramified `R`-algebra `T`,
`T ⊗ (S ⊗[P] Ω[P/R])` is isomorphic to `(T ⊗ S) ⊗[T ⊗ P] Ω[T ⊗ P/R]`.
This is the inverse of the isomorphism. See `cotangentSpaceTensorAlgebraEquiv`. -/
noncomputable
def Extension.cotangentSpaceTensorAlgebra :
    (P.tensorAlgebra T).CotangentSpace →ₗ[R] T ⊗[R] P.CotangentSpace :=
  (LinearMap.liftBaseChange _
    ⟨(P.cotangentSpaceTensorAlgebraAux T).toAddMonoidHom,
    P.cotangentSpaceTensorAlgebraAux_smul T⟩).restrictScalars R

lemma Extension.cotangentSpaceTensorAlgebra_tmul (a b c d) :
    P.cotangentSpaceTensorAlgebra T ((a ⊗ₜ b) ⊗ₜ .D _ _ (c ⊗ₜ d)) =
      (a * c) ⊗ₜ[R] b ⊗ₜ[P.Ring] (D R P.Ring) d := by
  dsimp [cotangentSpaceTensorAlgebra]
  rw [cotangentSpaceTensorAlgebraAux_apply_D]
  show (a * c) ⊗ₜ (b • (1 ⊗ₜ[P.Ring] (D R P.Ring) d)) = _
  rw [smul_tmul', smul_eq_mul, mul_one]

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.cotangentSpaceTensorAlgebra_comp_map :
    P.cotangentSpaceTensorAlgebra T ∘ₗ (((CotangentSpace.map (P.toTensorAlgebra
      T)).restrictScalars R).liftBaseChange T).restrictScalars R = .id := by
  ext t x
  dsimp
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero, tmul_zero]
  | add x y _ _ => simp only [map_add, smul_add, tmul_add, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, smul_zero, tmul_zero]
    | add x y _ _ => simp only [map_add, smul_add, tmul_add, *]
    | tmul a b =>
      rw [Derivation.tensorProductTo_tmul, ← smul_tmul, Algebra.Extension.CotangentSpace.map_tmul,
        smul_tmul', RingHom.algebraMap_toAlgebra', AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        TensorProduct.includeRight_apply, smul_tmul', smul_eq_mul, mul_one,
        Hom.toAlgHom_apply, toTensorAlgebra_toRingHom_apply,
        Extension.cotangentSpaceTensorAlgebra_tmul, mul_one]

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.cotangentSpaceTensorAlgebra_map_injective :
    Function.Injective (((CotangentSpace.map (P.toTensorAlgebra
      T)).restrictScalars R).liftBaseChange T) :=
  Function.LeftInverse.injective (DFunLike.congr_fun (P.cotangentSpaceTensorAlgebra_comp_map T))

attribute [local instance] TensorProduct.rightAlgebra in
/-- Given an `R`-extension `0 → I → P → S → 0` and a formally unramified `R`-algebra `T`,
`T ⊗ (S ⊗[P] Ω[P/R])` is isomorphic to `(T ⊗ S) ⊗[T ⊗ P] Ω[T ⊗ P/R]`. -/
noncomputable
def Extension.cotangentSpaceTensorAlgebraEquiv
    [Algebra.FormallyUnramified R T] :
    T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.tensorAlgebra T).CotangentSpace where
  __ := ((CotangentSpace.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T
  invFun := P.cotangentSpaceTensorAlgebra T
  left_inv := DFunLike.congr_fun (P.cotangentSpaceTensorAlgebra_comp_map T)
  right_inv := by
    intro x
    dsimp
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y _ _ => simp only [map_add, *]
    | tmul x y =>
      obtain ⟨y, rfl⟩ := tensorProductTo_surjective _ _ y
      induction y with
      | zero => simp only [map_zero, tmul_zero]
      | add x y _ _ => simp only [map_add, tmul_add, *]
      | tmul a b =>
        rw [Derivation.tensorProductTo_tmul, ← smul_tmul]
        generalize a • x = x
        induction x using TensorProduct.induction_on with
        | zero => simp only [map_zero, zero_tmul]
        | add x y _ _ => simp only [map_add, add_tmul, *]
        | tmul c d =>
          induction b using TensorProduct.induction_on with
          | zero => simp only [map_zero, tmul_zero]
          | add x y _ _ => simp only [map_add, tmul_add, *]
          | tmul a b =>
            letI : Algebra T (P.tensorAlgebra T).Ring := TensorProduct.leftAlgebra
            have : IsScalarTower R T (P.tensorAlgebra T).Ring :=
              inferInstanceAs (IsScalarTower R T (T ⊗[R] P.Ring))
            have : IsScalarTower T (P.tensorAlgebra T).Ring (T ⊗[R] S) :=
              .of_algebraMap_eq fun r ↦ show r ⊗ₜ 1 = r ⊗ₜ algebraMap P.Ring S 1 by rw [map_one]
            rw [Extension.cotangentSpaceTensorAlgebra_tmul, LinearMap.liftBaseChange_tmul,
              LinearMap.coe_restrictScalars, Algebra.Extension.CotangentSpace.map_tmul,
              mul_smul, ← tmul_smul, ← Derivation.map_smul_of_formallyUnramified, smul_tmul']
            congr 2
            · show c • (1 ⊗ₜ d) = _; rw [smul_tmul', smul_eq_mul, mul_one]
            · show a • (1 ⊗ₜ b) = _; rw [smul_tmul', smul_eq_mul, mul_one]

/-- Given an `R`-extension `0 → I → P → S → 0` and a flat `R`-algebra `T`,
The kernel of `T ⊗ P → T ⊗ S` is isomorphic to `T ⊗ I`. -/
noncomputable
def Extension.kerTensorAlgebra [Module.Flat R T] :
    T ⊗[R] RingHom.ker (algebraMap P.Ring S) ≃ₗ[T] (P.tensorAlgebra T).ker :=
  (IsScalarTower.toAlgHom R P.Ring S).toLinearMap.tensorKerEquiv T T

lemma Extension.kerTensorAlgebra_tmul [Module.Flat R T] (x y) :
    (P.kerTensorAlgebra T (x ⊗ₜ y)).1 = x ⊗ₜ y.1 :=
  LinearMap.tensorKer_tmul _ _ _ _ _

/-- (Implementation). Given an `R`-extension `0 → I → P → S → 0` and a flat `R`-algebra `T`,
This is the map `T ⊗ I → T ⊗ I/I²`. -/
noncomputable
def Extension.cotangentTensorAlgebraAux [Module.Flat R T] :
  (P.tensorAlgebra T).ker →ₗ[T] T ⊗[R] P.Cotangent :=
  ((Cotangent.mk.restrictScalars R).baseChange T ∘ₗ (P.kerTensorAlgebra T).symm.toLinearMap)

lemma Extension.cotangentTensorAlgebraAux_kerTensorAlgebra [Module.Flat R T] (x) :
    (P.cotangentTensorAlgebraAux T (P.kerTensorAlgebra T x)) =
      (Cotangent.mk.restrictScalars R).baseChange T x := by
  simp [cotangentTensorAlgebraAux]

lemma Extension.smul_le_ker_cotangentTensorAlgebraAux [Module.Flat R T] :
    ((P.tensorAlgebra T).ker • ⊤ : Submodule (P.tensorAlgebra T).Ring _).restrictScalars T ≤
      LinearMap.ker (P.cotangentTensorAlgebraAux T) := by
  intro x hx
  rw [Submodule.restrictScalars_mem] at hx
  refine Submodule.smul_induction_on hx ?_ fun _ _ ↦ add_mem
  clear x hx
  rintro a ha b -
  obtain ⟨x, hx⟩ := (P.kerTensorAlgebra T).surjective ⟨a, ha⟩
  obtain rfl : (P.kerTensorAlgebra T x).1 = a := congr_arg Subtype.val hx
  obtain ⟨y, rfl⟩ := ((P.kerTensorAlgebra T)).surjective b
  simp only [LinearMap.mem_ker]
  clear hx ha
  induction x with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, ZeroMemClass.coe_zero, zero_smul]
  | add x y _ _ =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, Submodule.coe_add, add_smul, zero_add, *]
  | tmul a b =>
    induction y with
    | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
    | add x y _ _ => simp only [LinearMap.map_add, LinearEquiv.map_add, smul_add, zero_add, *]
    | tmul c d =>
      trans (Cotangent.mk.restrictScalars R).baseChange T ((a * c) ⊗ₜ (b.1 • d))
      · rw [← Extension.cotangentTensorAlgebraAux_kerTensorAlgebra]
        congr 1
        simp only [Subtype.ext_iff, SetLike.val_smul, smul_eq_mul, kerTensorAlgebra_tmul]
        rw [TensorProduct.tmul_mul_tmul]
      · have : b.1 • Cotangent.mk d = 0 := by ext; simp [Cotangent.smul_eq_zero_of_mem _ b.2]
        simp only [LinearMap.baseChange_tmul, LinearMap.coe_restrictScalars,
          map_smul, this, tmul_zero]

/-- Given an `R`-extension `0 → I → P → S → 0` and a flat `R`-algebra `T`,
`T ⊗ (I/I²)` is isomorphic to `(T ⊗ I)/(T ⊗ I)²`.
This is the inverse of the isomorphism. See `cotangentTensorAlgebraEquiv`. -/
noncomputable
def Extension.cotangentTensorAlgebra [Module.Flat R T] :
    (P.tensorAlgebra T).Cotangent →ₗ[T] T ⊗[R] P.Cotangent := by
  refine ⟨(QuotientAddGroup.lift _ (P.cotangentTensorAlgebraAux T).toAddMonoidHom
    (P.smul_le_ker_cotangentTensorAlgebraAux T)).toAddHom, ?_⟩
  · intro a b
    have : IsScalarTower T (P.tensorAlgebra T).Ring (T ⊗[R] S) :=
      .of_algebraMap_eq fun r ↦ show r ⊗ₜ 1 = r ⊗ₜ algebraMap P.Ring S 1 by rw [map_one]
    obtain ⟨b, rfl⟩ := Cotangent.mk_surjective b
    simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, RingHom.id_apply,
      ← LinearMap.map_smul_of_tower]
    exact (P.cotangentTensorAlgebraAux T).map_smul a b

lemma Extension.cotangentTensorAlgebra_mk [Module.Flat R T] (x) :
    (P.cotangentTensorAlgebra T (.mk x)) = P.cotangentTensorAlgebraAux T x := rfl

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.cotangentTensorAlgebra_comp_map [Module.Flat R T] :
    P.cotangentTensorAlgebra T ∘ₗ ((Cotangent.map (P.toTensorAlgebra
      T)).restrictScalars R).liftBaseChange T = .id := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  dsimp
  simp only [one_smul, Extension.cotangentTensorAlgebra_mk]
  exact P.cotangentTensorAlgebraAux_kerTensorAlgebra T (1 ⊗ₜ x)

attribute [local instance] TensorProduct.rightAlgebra in
/-- Given an `R`-extension `0 → I → P → S → 0` and a flat `R`-algebra `T`,
`T ⊗ (I/I²)` is isomorphic to `(T ⊗ I)/(T ⊗ I)²`. -/
noncomputable
def Extension.cotangentTensorAlgebraEquiv [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.tensorAlgebra T).Cotangent where
  __ := ((Cotangent.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T
  invFun := P.cotangentTensorAlgebra T
  left_inv := DFunLike.congr_fun (P.cotangentTensorAlgebra_comp_map T)
  right_inv := by
    intro x
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨x, rfl⟩ := (P.kerTensorAlgebra T).surjective x
    simp only [cotangentTensorAlgebra_mk, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    induction x with
    | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
    | add x y _ _ => simp only [LinearMap.map_add, LinearEquiv.map_add, *]
    | tmul x y =>
      simp only [cotangentTensorAlgebraAux_kerTensorAlgebra, LinearMap.baseChange_tmul,
        LinearMap.coe_restrictScalars, LinearMap.liftBaseChange_tmul, Cotangent.map_mk,
        Hom.toAlgHom_apply, ← LinearMap.map_smul_of_tower]
      congr 1
      ext
      show x • (1 ⊗ₜ y.1) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Extension.kerTensorAlgebra_tmul]

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.cotangentTensorAlgebraEquiv_comp_h1Cotangentι [Module.Flat R T] :
    (P.cotangentTensorAlgebraEquiv T).toLinearMap ∘ₗ
      ((P.h1Cotangentι).restrictScalars R).baseChange T =
      h1Cotangentι.restrictScalars T ∘ₗ
      ((H1Cotangent.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T := by
  ext; simp [cotangentTensorAlgebraEquiv]

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.cotangentComplex_comp_cotangentTensorAlgebraEquiv [Module.Flat R T] :
    (P.tensorAlgebra T).cotangentComplex.restrictScalars T ∘ₗ
      (P.cotangentTensorAlgebraEquiv T).toLinearMap =
    ((CotangentSpace.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T ∘ₗ
        (P.cotangentComplex.restrictScalars R).baseChange T := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  dsimp [cotangentTensorAlgebraEquiv]
  simp only [one_smul, cotangentComplex_mk, CotangentSpace.map_tmul,
    map_one, Hom.toAlgHom_apply]

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.H1Cotangent.liftBaseChange_map_injective [Module.Flat R T] :
    Function.Injective
      (((H1Cotangent.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T) := by
  refine .of_comp (f := h1Cotangentι.restrictScalars T) ?_
  have : Function.Injective (((P.h1Cotangentι).restrictScalars R).baseChange T) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ h1Cotangentι_injective
  convert (P.cotangentTensorAlgebraEquiv T).injective.comp this using 1
  rw [← LinearMap.coe_comp, ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp,
    P.cotangentTensorAlgebraEquiv_comp_h1Cotangentι T]

/-- Given an `R`-extension `0 → I → P → S → 0` and a flat `R`-algebra `T`,
The `H¹(L)` associated to the extension `0 → T ⊗ I → T ⊗ P → T ⊗ S → 0` is isomorphic
to `T ⊗ H¹(L_P)`. This is the inverse of the isomorphism. See `h1CotangentTensorAlgebraEquiv`. -/
noncomputable
def Extension.h1CotangentTensorAlgebra [Module.Flat R T] :
  (P.tensorAlgebra T).H1Cotangent →ₗ[T] T ⊗[R] P.H1Cotangent :=
  letI e : T ⊗[R] P.H1Cotangent ≃ₗ[T]
    LinearMap.ker (((P.cotangentComplex.restrictScalars R)).baseChange T) :=
      ((P.cotangentComplex.restrictScalars R).tensorKerEquiv T T)
  e.symm.toLinearMap ∘ₗ ((P.cotangentTensorAlgebraEquiv T).symm.toLinearMap.restrict
    (p := (LinearMap.ker (P.tensorAlgebra T).cotangentComplex).restrictScalars T) <| by
  intro x hx
  simp only [LinearEquiv.coe_coe, LinearMap.mem_ker]
  apply P.cotangentSpaceTensorAlgebra_map_injective T
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hx
  rw [map_zero, ← hx, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply,
    ← Extension.cotangentComplex_comp_cotangentTensorAlgebraEquiv]
  simp only [LinearEquiv.coe_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, LinearEquiv.apply_symm_apply, LinearMap.map_coe_ker])

attribute [local instance] TensorProduct.rightAlgebra in
lemma Extension.comp_h1CotangentTensorAlgebra [Module.Flat R T] :
  ((H1Cotangent.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T ∘ₗ
    P.h1CotangentTensorAlgebra T = .id := by
  ext a
  refine (DFunLike.congr_fun (P.cotangentTensorAlgebraEquiv_comp_h1Cotangentι T) _).symm.trans ?_
  refine (P.cotangentTensorAlgebraEquiv T).eq_symm_apply.mp ?_
  exact (P.cotangentComplex.restrictScalars R).lTensor_ker_subtype_tensorKerEquiv_symm _ _ _

attribute [local instance] TensorProduct.rightAlgebra in
/-- Given an `R`-extension `0 → I → P → S → 0` and a flat `R`-algebra `T`,
The `H¹(L)` associated to the extension `0 → T ⊗ I → T ⊗ P → T ⊗ S → 0` is isomorphic
to `T ⊗ H¹(L_P)`. -/
noncomputable
def Extension.h1CotangentTensorAlgebraEquiv [Module.Flat R T] :
    T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.tensorAlgebra T).H1Cotangent where
  __ := ((H1Cotangent.map (P.toTensorAlgebra T)).restrictScalars R).liftBaseChange T
  invFun := P.h1CotangentTensorAlgebra T
  left_inv x := by
    apply H1Cotangent.liftBaseChange_map_injective
    exact DFunLike.congr_fun (P.comp_h1CotangentTensorAlgebra T) _
  right_inv := DFunLike.congr_fun (P.comp_h1CotangentTensorAlgebra T)

end Algebra
