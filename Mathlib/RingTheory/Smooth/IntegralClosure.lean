/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Flat.Basic


/-!
# Smooth base change commutes with integral closure

In this file we aim to prove that smooth base change commutes with integral closure.
We define the map
`TensorProduct.toIntegralClosure : S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B)`
and (TODO) show that it is bijective when `S` is `R`-smooth.

## Main results
- `TensorProduct.toIntegralClosure_injective_of_flat`:
  If `S` is `R`-flat, then `TensorProduct.toIntegralClosure` is injective.
- `TensorProduct.toIntegralClosure_mvPolynomial_bijective`:
  If `S = MvPolynomial σ R`, then `TensorProduct.toIntegralClosure` is bijective.
- `TensorProduct.toIntegralClosure_bijective_of_isLocalization`:
  If `S = Localization M`, then `TensorProduct.toIntegralClosure` is bijective.

## TODO (@erdOne)
Show that `TensorProduct.toIntegralClosure` is bijective when `S` is `R`-smooth.
-/

@[expose] public section

open Polynomial TensorProduct

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]

variable (R S) in
/-- The comparison map from `S ⊗[R] integralClosure R B` to `integralClosure S (S ⊗[R] B)`.
This is injective when `S` is `R`-flat, and (TODO) bijective when `S` is `R`-smooth. -/
def TensorProduct.toIntegralClosure
    (B : Type*) [CommRing B] [Algebra R B] :
    S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (.id _ _) (integralClosure R B).val).codRestrict _ fun x ↦ by
  induction x with
  | zero => simp
  | add x y _ _ => rw [map_add]; exact add_mem ‹_› ‹_›
  | tmul x y =>
    convert ((y.2.map (Algebra.TensorProduct.includeRight
      (R := R) (A := S))).tower_top (A := S)).smul x
    simp [smul_tmul']

lemma TensorProduct.toIntegralClosure_injective_of_flat [Module.Flat R S] :
    Function.Injective (toIntegralClosure R S B) := by
  refine Function.Injective.of_comp (f := (integralClosure _ _).val) ?_
  rw [← AlgHom.coe_comp, toIntegralClosure, AlgHom.val_comp_codRestrict]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (integralClosure R B).val.toLinearMap Subtype.val_injective

/-- "Base change preserves integral closure" is stable under composition. -/
lemma TensorProduct.toIntegralClosure_bijective_of_tower
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (H : Function.Bijective (toIntegralClosure R S B))
    (H' : Function.Bijective (toIntegralClosure S T (S ⊗[R] B))) :
    Function.Bijective (toIntegralClosure R T B) := by
  let e := (Algebra.TensorProduct.cancelBaseChange ..).symm.trans <|
      (Algebra.TensorProduct.congr (.refl (R := T) (A₁ := T)) (.ofBijective _ H)).trans <|
      (AlgEquiv.ofBijective _ H').trans <|
      (AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.cancelBaseChange ..))
  convert e.bijective
  rw [← e.coe_algHom]
  congr 1
  ext; simp [e, toIntegralClosure]

/-- "Base change preserves integral closure" can be checked Zariski-locally. -/
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway
    {s : Set S} (hs : Ideal.span s = ⊤) (Sᵣ : s → Type*) [∀ r, CommRing (Sᵣ r)]
    [∀ r, Algebra S (Sᵣ r)] [∀ r, Algebra R (Sᵣ r)] [∀ r, IsScalarTower R S (Sᵣ r)]
    [∀ r, IsLocalization.Away r.1 (Sᵣ r)]
    (H : ∀ r, Function.Bijective (toIntegralClosure R (Sᵣ r) B)) :
    Function.Bijective (toIntegralClosure R S B) := by
  have (r : s) : IsLocalizedModule.Away r.1
      (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
      (AlgHom.id R (integralClosure R B))).toAlgebra
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
    ext; simp [RingHom.algebraMap_toAlgebra]
  let φ (r : s) : integralClosure S (S ⊗[R] B) →ₐ[S] integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B) :=
    ((Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).comp
      (integralClosure S (S ⊗[R] B)).val).codRestrict
        ((integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B)).restrictScalars S) <| by
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Subalgebra.mem_restrictScalars, Subtype.forall, mem_integralClosure_iff]
    exact fun a ha ↦ (ha.map _).tower_top
  have (r : s) : IsLocalizedModule.Away r.1 (φ r).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
          (AlgHom.id R B)).toAlgebra
    let := (φ r).toAlgebra
    have : IsScalarTower (integralClosure S (S ⊗[R] B)) (integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B))
        (Sᵣ r ⊗[R] B) := .of_algebraMap_eq' rfl
    have : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] B) (Submonoid.powers r.1))
        (Sᵣ r ⊗[R] B) := by
      refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
      ext; simp [RingHom.algebraMap_toAlgebra]
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    exact IsLocalization.integralClosure ..
  refine bijective_of_isLocalized_span s hs (F := (toIntegralClosure R S B).toLinearMap)
    (fun r ↦ (Sᵣ r) ⊗[R] integralClosure R B)
    (fun r ↦ (Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).toLinearMap)
    (fun r ↦ integralClosure (Sᵣ r) ((Sᵣ r) ⊗[R] B))
    (fun r ↦ (φ r).toLinearMap) fun r ↦ ?_
  convert show Function.Bijective ((toIntegralClosure R (Sᵣ r) B).toLinearMap.restrictScalars S)
    from H r using 1
  congr!
  refine IsLocalizedModule.ext (.powers r.1) (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
    (AlgHom.id R (integralClosure R B))).toLinearMap
    (IsLocalizedModule.map_units (S := .powers r.1) (φ r).toLinearMap) ?_
  ext x
  exact congr($(IsLocalizedModule.map_apply (.powers r.1)
      ((Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap)
      (φ r).toLinearMap (toIntegralClosure R S B).toLinearMap (1 ⊗ₜ x)).1)

attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Base changing to `MvPolynomial σ R` preserves integral closure. -/
lemma TensorProduct.toIntegralClosure_mvPolynomial_bijective {σ : Type*} :
    Function.Bijective (toIntegralClosure R (MvPolynomial σ R) B) := by
  classical
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨x, hx⟩
  let e₀ : MvPolynomial σ R ⊗[R] B ≃ₐ[R] MvPolynomial σ B :=
    MvPolynomial.scalarRTensorAlgEquiv
  let e : MvPolynomial σ R ⊗[R] B ≃ₐ[MvPolynomial σ R] MvPolynomial σ B :=
    { toRingEquiv := e₀.toRingEquiv, commutes' r := by
        change e₀.toRingHom.comp (algebraMap _ _) r = _
        congr 1
        ext <;> simp [e₀, MvPolynomial.scalarRTensorAlgEquiv, MvPolynomial.coeff_map,
          ← Algebra.algebraMap_eq_smul_one, apply_ite (algebraMap _ _), MvPolynomial.coeff_X'] }
  have := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp (hx.map e)
  obtain ⟨y, hy⟩ : e x ∈ RingHom.range (MvPolynomial.map (integralClosure R B).val.toRingHom) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr ?_
    simp [Set.subset_def, mem_integralClosure_iff, MvPolynomial.mem_coeffs_iff,
      @forall_comm B, this]
  refine ⟨MvPolynomial.scalarRTensorAlgEquiv.symm y, Subtype.ext <| e.injective (.trans ?_ hy)⟩
  obtain ⟨y, rfl⟩ := (MvPolynomial.scalarRTensorAlgEquiv (R := R)).surjective y
  dsimp [TensorProduct.toIntegralClosure, e]
  simp only [AlgEquiv.symm_apply_apply]
  have : e₀.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R)) (integralClosure R B).val) =
      (MvPolynomial.mapAlgHom (integralClosure R B).val).comp
      MvPolynomial.scalarRTensorAlgEquiv.toAlgHom := by
    ext <;> simp [e₀, -MvPolynomial.mapAlgHom_apply, MvPolynomial.mapAlgHom, MvPolynomial.coeff_map,
      MvPolynomial.scalarRTensorAlgEquiv]
  exact congr($this y)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Localization preserves integral closure. -/
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalization
    (M : Submonoid R) [IsLocalization M S] :
    Function.Bijective (toIntegralClosure R S B) := by
  classical
  let φ : integralClosure R B →ₐ[R] integralClosure S (S ⊗[R] B) :=
    AlgHom.codRestrict (Algebra.TensorProduct.includeRight.comp (integralClosure R B).val)
      ((integralClosure S (S ⊗[R] B)).restrictScalars R) fun ⟨x, hx⟩ ↦ by
    refine .of_comp (f := algebraMap R S) ?_
    convert RingHom.IsIntegralElem.map hx
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom
    simp [← IsScalarTower.algebraMap_eq]
  let := φ.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower (integralClosure R B) (integralClosure S (S ⊗[R] B)) (S ⊗[R] B) :=
    .of_algebraMap_eq' rfl
  have := IsLocalization.integralClosure (S := B) M (Rf := S) (Sf := S ⊗[R] B)
  convert (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (integralClosure R B) M)
    (S ⊗[R] integralClosure R B) (integralClosure S (S ⊗[R] B))).bijective
  rw [← AlgHom.coe_restrictScalars' R, ← AlgEquiv.coe_restrictScalars' R, ← AlgEquiv.coe_algHom]
  congr 1
  ext1
  · apply IsLocalization.algHom_ext M; ext
  · ext x
    dsimp [toIntegralClosure]
    simp [← Algebra.TensorProduct.right_algebraMap_apply]
    rfl
