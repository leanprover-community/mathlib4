/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.Algebra.FiveLemma
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for the naive cotangent complex

This file shows that the cotangent space and first homology of the naive cotangent complex
commute with base change.

## Main results

- `Algebra.Extension.tensorCotangentSpace`: If `T` is an `R`-algebra, there is a `T`-linear
  isomorphism `T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange).CotangentSpace`.
- `Algebra.Extension.tensorCotangent'`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`.
- `Algebra.Extension.tensorH1Cotangent'`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`.
- `Algebra.tensorH1CotangentOfFlat`: Flat base change commutes with `H1Cotangent`.

-/

suppress_compilation

universe u

open TensorProduct

namespace Algebra

namespace Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u} R S)
variable (T : Type*) [CommRing T] [Algebra R T]

/-- The cotangent space of an extension commutes with base change. -/
noncomputable def tensorCotangentSpace :
    T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange (T := T)).CotangentSpace :=
  letI := P.algebraBaseChange T
  letI : Algebra S (T ⊗[R] S) := TensorProduct.rightAlgebra
  letI : Algebra P.Ring (T ⊗[R] S) := Algebra.compHom _ (algebraMap P.Ring S)
  haveI : IsScalarTower R P.Ring (T ⊗[R] S) :=
    .of_algebraMap_eq fun x ↦ by
      rw [TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.tmul_one_eq_one_tmul, IsScalarTower.algebraMap_apply R P.Ring]
      rfl
  letI PT : Extension T (T ⊗[R] S) := P.baseChange
  haveI : IsPushout R T P.Ring PT.Ring := by
    convert TensorProduct.isPushout (R := R) (T := P.Ring) (S := T)
    exact Algebra.algebra_ext _ _ fun _ ↦ rfl
  haveI : IsScalarTower P.Ring PT.Ring (T ⊗[R] S) := .of_algebraMap_eq' rfl
  (IsTensorProduct.assocOfMapSMul (TensorProduct.mk R T S) (isTensorProduct _ _ _)
    (TensorProduct.mk _ _ _) (isTensorProduct _ _ _) (by simp [Algebra.smul_def])
    (by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra])).symm ≪≫ₗ
  (AlgebraTensorModule.cancelBaseChange _ PT.Ring PT.Ring _ _).symm.restrictScalars T ≪≫ₗ
  (AlgebraTensorModule.congr (LinearEquiv.refl PT.Ring (T ⊗[R] S))
    (KaehlerDifferential.tensorKaehlerEquiv R T P.Ring PT.Ring)).restrictScalars T

attribute [local instance] algebraBaseChange in
@[simp]
lemma tensorCotangentSpace_tmul_tmul (t : T) (s : S) (x : Ω[P.Ring⁄R]) :
    P.tensorCotangentSpace T (t ⊗ₜ (s ⊗ₜ x)) = t ⊗ₜ s ⊗ₜ KaehlerDifferential.map _ _ _ _ x := by
  simp only [tensorCotangentSpace, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    ← mk_apply s x, IsTensorProduct.assocOfMapSMul_symm_tmul]
  simp only [mk_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply]
  have this : x ∈ Submodule.span P.Ring (Set.range (KaehlerDifferential.D R P.Ring)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction this using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => simp [tmul_add, hx, hy]
  | mem y hy =>
    obtain ⟨y, rfl⟩ := hy
    simp
  | smul a x _ hx =>
    rw [tmul_smul, ← algebraMap_smul (P.baseChange (T := T)).Ring a, LinearEquiv.map_smul,
      tmul_smul, hx, LinearMap.map_smul, ← algebraMap_smul (P.baseChange (T := T)).Ring a,
      tmul_smul]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma tensorCotangentSpace_tmul (t : T) (x : P.CotangentSpace) :
    P.tensorCotangentSpace T (t ⊗ₜ x) = t • CotangentSpace.map (P.toBaseChange T) x := by
  dsimp only [CotangentSpace] at x
  induction x with
  | zero => rw [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, smul_zero]
  | add x y hx hy => rw [tmul_add, LinearEquiv.map_add, LinearMap.map_add, smul_add, hx, hy]
  | tmul s y =>
  simp [tensorCotangentSpace_tmul_tmul, CotangentSpace.map_tmul_eq_tmul_map,
    smul_tmul', Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end Extension

end Algebra

/-!
### Auxiliary lemma to be moved

The following lemma belongs in `Mathlib.RingTheory.Ideal.Cotangent`.
-/

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (T : Type*) [CommRing T] [Algebra R T]
variable (I : Ideal S)

/-- A linear isomorphism between cotangent spaces induced by an equality of ideals. -/
def Cotangent.equivOfEq (I J : Ideal S) (hIJ : I = J) :
    I.Cotangent ≃ₗ[S] J.Cotangent where
  __ := Cotangent.lift (J.toCotangent ∘ₗ LinearEquiv.ofEq I J hIJ) <| fun x y ↦ by
    simp [toCotangent_eq_zero, ← hIJ, sq, mul_mem_mul]
  invFun := Cotangent.lift (I.toCotangent ∘ₗ LinearEquiv.ofEq J I hIJ.symm) <| fun x y ↦ by
    simp [toCotangent_eq_zero, hIJ, sq, mul_mem_mul]
  left_inv x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_toCotangent, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply]
    rfl
  right_inv x := by
    obtain ⟨x, rfl⟩ := J.toCotangent_surjective x
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_toCotangent, LinearMap.coe_comp,
      LinearEquiv.coe_coe, Function.comp_apply]
    rfl

@[simp]
lemma Cotangent.equivOfEq_toCotangent (I J : Ideal S) (hIJ : I = J) (x : I) :
    Cotangent.equivOfEq I J hIJ (I.toCotangent x) = J.toCotangent (LinearEquiv.ofEq I J hIJ x) :=
  rfl

end Ideal

namespace Algebra

namespace Generators

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*}
variable (P : Generators R S ι)
variable (T : Type u) [CommRing T] [Algebra R T]

/-- The canonical hom from the base change of `P.toExtension` to the extension
corresponding to `P.baseChange`. -/
noncomputable
def baseChangeFromBaseChange :
    (P.toExtension.baseChange (T := T)).Hom (P.baseChange (T := T)).toExtension where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).toRingHom
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, Extension.baseChange,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply, MvPolynomial.algebraMap_eq]
    change (MvPolynomial.algebraTensorAlgEquiv R T) (x ⊗ₜ[R] 1) = MvPolynomial.C x
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_one, smul_def,
      MvPolynomial.algebraMap_eq, mul_one]
  algebraMap_toRingHom x := by
    simp only [Extension.baseChange, toExtension_Ring,
      AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
      algebraMap_apply, algebraMap_self, RingHomCompTriple.comp_apply] at x ⊢
    change (MvPolynomial.aeval (P.baseChange T).val) (MvPolynomial.algebraTensorAlgEquiv R T x) = _
    induction x with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, RingHom.map_add, map_add, hx, hy]
    | tmul t x =>
      simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul]
      rw [Algebra.smul_def]
      simp only [TensorProduct.algebraMap_apply, algebraMap_self, RingHom.id_apply, baseChange,
        ofSurjective, AlgHom.toRingHom_eq_coe, MvPolynomial.aeval_map_algebraMap]
      induction x using MvPolynomial.induction_on with
      | C r =>
        simp only [MvPolynomial.algHom_C, TensorProduct.algebraMap_apply,
          TensorProduct.tmul_mul_tmul, mul_one, RingHom.algebraMap_toAlgebra,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [mul_comm, ← Algebra.smul_def, ← smul_tmul', ← tmul_smul, Algebra.smul_def, mul_one]
        simp
      | mul_X p i hp =>
        simp only [map_mul, MvPolynomial.aeval_X]
        rw [← mul_assoc, hp]
        simp [RingHom.algebraMap_toAlgebra]
      | add p q hp hq =>
        simp only [map_add, mul_add, hp, hq]
        rw [tmul_add, RingHom.map_add]

noncomputable
def baseChangeToBaseChange :
    (P.baseChange (T := T)).toExtension.Hom (P.toExtension.baseChange (T := T)) where
  toRingHom := (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom
  algebraMap_toRingHom x := by
    have := (P.baseChangeFromBaseChange T).algebraMap_toRingHom <|
      (MvPolynomial.algebraTensorAlgEquiv R T).symm.toRingHom x
    simp only [toExtension_Ring,
      baseChangeFromBaseChange, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.symm_toRingEquiv, RingHom.coe_coe, algebraMap_apply,
      algebraMap_self, RingHomCompTriple.comp_apply] at this
    convert this.symm
    change _ = (MvPolynomial.aeval (P.baseChange T).val)
      ((MvPolynomial.algebraTensorAlgEquiv R T) (((MvPolynomial.algebraTensorAlgEquiv R T)).symm x))
    simp only [algebraMap_self, toExtension_Ring,
      algebraMap_apply, MvPolynomial.map_aeval, RingHomCompTriple.comp_eq, baseChange_val,
      RingHom.id_apply, MvPolynomial.coe_eval₂Hom, AlgEquiv.apply_symm_apply]
    rfl
  toRingHom_algebraMap x := by
    simp only [toExtension_Ring, AlgEquiv.toRingEquiv_eq_coe,
      AlgEquiv.symm_toRingEquiv, RingEquiv.toRingHom_eq_coe, MvPolynomial.algebraMap_eq,
      algebraMap_self, RingHom.id_apply]
    change (MvPolynomial.algebraTensorAlgEquiv R T).symm _ = _
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl

end Generators

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u, u, u} R S)
variable (T : Type u) [CommRing T] [Algebra R T]

namespace Extension

attribute [local instance] SMulCommClass.of_commMonoid

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `Cotangent.val` as a linear isomorphism. -/
@[simps]
def valEquiv : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where
  toFun := Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp
  left_inv x := rfl
  right_inv x := rfl

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`. -/
noncomputable def tensorCotangent' [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  let e₀ : T ⊗[R] P.Cotangent ≃ₗ[T] T ⊗[R] P.ker.Cotangent :=
    AlgebraTensorModule.congr (LinearEquiv.refl T T) (P.valEquiv.restrictScalars R)
  let e₁ := P.ker.tensorCotangentEquiv R T
  have : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker) = (P.baseChange (T := T)).ker := by
    simp only [Extension.ker, RingHom.algebraMap_toAlgebra]
    symm
    exact Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
      P.algebraMap_surjective
  let e₂ : (Ideal.map (algebraMap P.Ring (T ⊗[R] P.Ring)) P.ker).Cotangent ≃ₗ[T]
      (P.baseChange (T := T)).ker.Cotangent :=
    (Ideal.Cotangent.equivOfEq _ _ this).restrictScalars T
  let e₃ : (P.baseChange (T := T)).ker.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
    (P.baseChange (T := T)).valEquiv.symm.restrictScalars T
  e₀ ≪≫ₗ e₁ ≪≫ₗ e₂ ≪≫ₗ e₃

@[simp]
lemma tensorCotangent'_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) :
    P.tensorCotangent' T (t ⊗ₜ x) = t • Cotangent.map (P.toBaseChange T) x := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangent', LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, valEquiv_apply, Cotangent.val_mk,
    Ideal.tensorCotangentEquiv_tmul, map_smul, valEquiv_symm_apply, Cotangent.map_mk,
    Hom.toAlgHom_apply]
  rfl

/-!
### Part 2: H1Cotangent base change

This section establishes that `H1Cotangent` commutes with flat base change.
-/

/-- The canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange).H1Cotangent`. -/
noncomputable
def tensorToH1Cotangent :
    T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  let _ : Algebra S (T ⊗[R] S) := TensorProduct.includeRight.toRingHom.toAlgebra
  LinearMap.liftBaseChange T <|
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

@[simp]
lemma tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) :
    (P.tensorToH1Cotangent T (t ⊗ₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val :=
  rfl

lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
      (M₄ := T ⊗[R] P.Cotangent) (N₄ := (P.baseChange (T := T)).Cotangent)
      (M₅ := T ⊗[R] P.CotangentSpace) (N₅ := (P.baseChange (T := T)).CotangentSpace)
    0
    0
    (((h1Cotangentι (P := P)).restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    0
    0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    0
    0
    ((P.tensorToH1Cotangent T).restrictScalars R)
    ((P.tensorCotangent' T).restrictScalars R)
    ((P.tensorCotangentSpace T).restrictScalars R)
  · simp
  · simp
  · ext t x
    simp
  · ext t x
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp only [LinearMap.exact_zero_iff_injective]
    apply Module.Flat.lTensor_preserves_injective_linearMap
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    simp only [LinearMap.coe_restrictScalars]
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · simp only [LinearMap.coe_restrictScalars]
    apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangent' T).bijective
  · exact (P.tensorCotangentSpace T).injective

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`. -/
noncomputable def tensorH1Cotangent' [Module.Flat R T] :
    T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

end Extension

end

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Flat base change commutes with `H1Cotangent`. -/
noncomputable def tensorH1CotangentOfFlat (T : Type u) [CommRing T] [Algebra R T]
    [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  let P : Extension R S := (Generators.self R S).toExtension
  let e : T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
    P.tensorH1Cotangent' T
  let PT : Extension T (T ⊗[R] S) := P.baseChange
  let PT' : Extension T (T ⊗[R] S) := ((Generators.self R S).baseChange T).toExtension
  let f₁ : PT.Hom PT' := (Generators.self R S).baseChangeFromBaseChange T
  let f₂ : PT'.Hom PT := (Generators.self R S).baseChangeToBaseChange T
  let e₂ : PT.H1Cotangent ≃ₗ[T] PT'.H1Cotangent :=
    (Extension.H1Cotangent.equiv f₁ f₂).restrictScalars T
  e ≪≫ₗ e₂ ≪≫ₗ ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.restrictScalars T

end Algebra
