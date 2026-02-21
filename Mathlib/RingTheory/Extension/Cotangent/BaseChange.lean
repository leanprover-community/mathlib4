/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for the naive cotangent complex

This file shows that the cotangent space and first homology of the naive cotangent complex
commute with base change.

## Main results

- `Algebra.Extension.tensorCotangentSpace`: If `T` is an `R`-algebra, there is a `T`-linear
  isomorphism `T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange).CotangentSpace`.

## TODOs (@chrisflav)

- Show that `P.Cotangent` commutes with flat base change.
- Show that `P.H1Cotangent` commutes with flat base change.
-/

public section

universe u

open TensorProduct

namespace Algebra

namespace Extension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : Extension.{u} R S)
variable (T : Type*) [CommRing T] [Algebra R T]

/-- The cotangent space of an extension commutes with base change. -/
noncomputable
def tensorCotangentSpace (P : Extension.{u} R S) (T : Type*) [CommRing T] [Algebra R T] :
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
