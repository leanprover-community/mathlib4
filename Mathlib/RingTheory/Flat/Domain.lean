/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Localization

/-!
# Flat modules in domains

We show that the tensor product of two injective linear maps is injective if the sources are flat
and the ring is an integral domain.
-/

universe u

variable {R M N : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

open TensorProduct Function

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
/-- Tensor product of injective maps over domains are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat`
for different flatness conditions but without the domain assumption. -/
lemma TensorProduct.map_injective_of_flat_flat_of_isDomain
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [H : Module.Flat R P] [Module.Flat R Q]
    (hf : Injective f) (hg : Injective g) : Injective (TensorProduct.map f g) := by
  let K := FractionRing R
  refine .of_comp (f := TensorProduct.mk R K _ 1) ?_
  have H₁ := TensorProduct.map_injective_of_flat_flat (f.baseChange K) (g.baseChange K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)
  have H₂ := (AlgebraTensorModule.cancelBaseChange R K K (K ⊗[R] P) Q).symm.injective
  have H₃ := (AlgebraTensorModule.cancelBaseChange R K K (K ⊗[R] M) N).injective
  have H₄ := (AlgebraTensorModule.assoc R R K K P Q).symm.injective
  have H₅ := (AlgebraTensorModule.assoc R R K K M N).injective
  have H₆ := Module.Flat.rTensor_preserves_injective_linearMap (M := P ⊗[R] Q)
    (Algebra.linearMap R K) (FaithfulSMul.algebraMap_injective R K)
  have H₇ := (TensorProduct.lid R (P ⊗[R] Q)).symm.injective
  convert H₅.comp <| H₃.comp <| H₁.comp <| H₂.comp <| H₄.comp <| H₆.comp <| H₇
  dsimp only [← LinearMap.coe_comp, ← LinearEquiv.coe_toLinearMap,
    ← @LinearMap.coe_restrictScalars R K]
  congr! 1
  ext p q
  -- `simp` solves the goal but it times out
  change (1 : K) ⊗ₜ[R] (f p ⊗ₜ[R] g q) = (AlgebraTensorModule.assoc R R K K M N)
    (((1 : K) • (algebraMap R K) 1 ⊗ₜ[R] f p) ⊗ₜ[R] g q)
  simp only [map_one, one_smul, AlgebraTensorModule.assoc_tmul]

variable {ι κ : Type*} {v : ι → M} {w : κ → N} {s : Set ι} {t : Set κ}

/-- Tensor product of linearly independent families is linearly independent over domains.
This is true over non-domains if one of the modules is flat.
See `LinearIndependent.tmul_of_flat_left`. -/
lemma LinearIndependent.tmul_of_isDomain (hv : LinearIndependent R v) (hw : LinearIndependent R w) :
    LinearIndependent R fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert (TensorProduct.map_injective_of_flat_flat_of_isDomain _ _ hv hw).comp
    (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- Tensor product of linearly independent families is linearly independent over domains.
This is true over non-domains if one of the modules is flat.
See `LinearIndepOn.tmul_of_flat_left`. -/
nonrec lemma LinearIndepOn.tmul_of_isDomain (hv : LinearIndepOn R v s) (hw : LinearIndepOn R w t) :
    LinearIndepOn R (fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_isDomain hw).comp _ (Equiv.Set.prod _ _).injective:)
