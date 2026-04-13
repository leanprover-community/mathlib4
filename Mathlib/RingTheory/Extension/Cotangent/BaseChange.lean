/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.CotangentBaseChange
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Base change for the naive cotangent complex

This file shows that the cotangent space and first homology of the naive cotangent complex
commute with base change.

## Main results

- `Algebra.Extension.tensorCotangentSpace`: If `T` is an `R`-algebra, there is a `T`-linear
  isomorphism `T ⊗[R] P.CotangentSpace ≃ₗ[T] (P.baseChange).CotangentSpace`.
- `Algebra.Extension.tensorCotangentOfFlat`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`.
- `Algebra.Extension.tensorH1CotangentOfFlat`: If `T` is flat over `R`, there is a `T`-linear
  isomorphism `T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`.
- `Algebra.tensorH1CotangentOfFlat`: Flat base change commutes with `H1Cotangent`.

-/

public section

universe u

open TensorProduct

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable {R S} (P : Extension.{u} R S)
variable (T : Type*) [CommRing T] [Algebra R T]

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange).Cotangent`. -/
noncomputable def tensorCotangentOfFlat [Module.Flat R T] :
    T ⊗[R] P.Cotangent ≃ₗ[T] (P.baseChange (T := T)).Cotangent :=
  AlgebraTensorModule.congr (.refl T T) (P.cotangentEquivCotangentKer.restrictScalars R) ≪≫ₗ
    P.ker.tensorCotangentEquiv R T ≪≫ₗ
    (Ideal.Cotangent.equivOfEq _ _ (P.ker_baseChange T).symm).restrictScalars T ≪≫ₗ
    (P.baseChange (T := T)).cotangentEquivCotangentKer.symm.restrictScalars T

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma tensorCotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.Cotangent) :
    P.tensorCotangentOfFlat T (t ⊗ₜ x) = t • Cotangent.map (P.toBaseChange T) x := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [tensorCotangentOfFlat, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply, cotangentEquivCotangentKer_apply,
    Cotangent.val_mk, Ideal.tensorCotangentEquiv_tmul, map_smul, Cotangent.map_mk,
    Hom.toAlgHom_apply, Ideal.Cotangent.equivOfEq_toCotangent]
  rfl

/-- The canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange).H1Cotangent`. -/
@[expose]
noncomputable
def tensorToH1Cotangent : T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  letI : Algebra S (T ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  LinearMap.liftBaseChange T <|
    (Extension.H1Cotangent.map (P.toBaseChange T)).restrictScalars R

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma tensorToH1Cotangent_tmul (t : T) (x : P.H1Cotangent) :
    (P.tensorToH1Cotangent T (t ⊗ₜ x)).val = t • Cotangent.map (P.toBaseChange T) x.val :=
  rfl

/-- If `T` is `R`-flat, the canonical map `T ⊗[R] P.H1Cotangent →ₗ[T] (P.baseChange T).H1Cotangent`
is bijective. -/
lemma tensorToH1Cotangent_bijective_of_flat [Module.Flat R T] :
    Function.Bijective (P.tensorToH1Cotangent T) := by
  -- We apply the five lemma.
  apply LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective (M₁ := Unit)
      (N₁ := Unit) (M₂ := Unit) (N₂ := Unit)
    -- The row `0 → 0 → T ⊗ H¹(P) → T ⊗ P.Cotangent → T ⊗ P.CotangentSpace`.
    0 0
    ((P.h1Cotangentι.restrictScalars R).lTensor T)
    ((P.cotangentComplex.restrictScalars R).lTensor T)
    -- The row `0 → 0 → H¹(T ⊗ P) → (T ⊗ P).Cotangent → (T ⊗ P).CotangentSpace`.
    0 0
    (h1Cotangentι.restrictScalars R)
    ((P.baseChange (T := T)).cotangentComplex.restrictScalars R)
    -- The vertical maps induced by base change.
    0 0
    ((P.tensorToH1Cotangent T).restrictScalars R)
    ((P.tensorCotangentOfFlat T).restrictScalars R)
    ((P.tensorCotangentSpace T).restrictScalars R)
  · simp
  · simp
  · ext
    simp
  · ext
    simp [CotangentSpace.map_cotangentComplex]
  · tauto
  · simp only [LinearMap.exact_zero_iff_injective]
    apply Module.Flat.lTensor_preserves_injective_linearMap
    exact h1Cotangentι_injective
  · apply Module.Flat.lTensor_exact
    exact P.exact_hCotangentι_cotangentComplex
  · tauto
  · rw [LinearMap.exact_zero_iff_injective]
    simp only [LinearMap.coe_restrictScalars]
    exact h1Cotangentι_injective
  · apply exact_hCotangentι_cotangentComplex
  · tauto
  · simp
  · exact (P.tensorCotangentOfFlat T).bijective
  · exact (P.tensorCotangentSpace T).injective

/-- If `T` is flat over `R`, there is a `T`-linear isomorphism
`T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange).H1Cotangent`. -/
@[expose]
noncomputable def tensorH1CotangentOfFlat [Module.Flat R T] :
    T ⊗[R] P.H1Cotangent ≃ₗ[T] (P.baseChange (T := T)).H1Cotangent :=
  LinearEquiv.ofBijective (P.tensorToH1Cotangent T)
    (P.tensorToH1Cotangent_bijective_of_flat T)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
lemma tensorH1CotangentOfFlat_tmul [Module.Flat R T] (t : T) (x : P.H1Cotangent) :
    P.tensorH1CotangentOfFlat T (t ⊗ₜ x) = t • H1Cotangent.map (P.toBaseChange T) x :=
  rfl

end Extension

/-- Flat base change commutes with `H1Cotangent`. -/
noncomputable def tensorH1CotangentOfFlat (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T] :
    T ⊗[R] H1Cotangent R S ≃ₗ[T] H1Cotangent T (T ⊗[R] S) :=
  (Generators.self R S).toExtension.tensorH1CotangentOfFlat T ≪≫ₗ
    (Extension.H1Cotangent.equiv
      ((Generators.self R S).baseChangeFromBaseChange T)
      ((Generators.self R S).baseChangeToBaseChange T)).restrictScalars T ≪≫ₗ
    ((Generators.self R S).baseChange (T := T)).equivH1Cotangent.restrictScalars T

attribute [local instance] TensorProduct.rightAlgebra in
lemma tensorH1CotangentOfFlat_tmul (T : Type*) [CommRing T] [Algebra R T] [Module.Flat R T]
    (t : T) (x : H1Cotangent R S) :
    tensorH1CotangentOfFlat R S T (t ⊗ₜ x) = t • H1Cotangent.map _ _ _ _ x := by
  simp only [tensorH1CotangentOfFlat, LinearEquiv.trans_apply,
    Extension.tensorH1CotangentOfFlat_tmul, map_smul, LinearEquiv.restrictScalars_apply,
    Extension.H1Cotangent.equiv, LinearEquiv.coe_mk, Generators.equivH1Cotangent,
    Generators.H1Cotangent.equiv]
  rw [← Extension.H1Cotangent.map_comp_apply, ← Extension.H1Cotangent.map_comp_apply,
    H1Cotangent.map, Extension.H1Cotangent.map_eq]

end Algebra
