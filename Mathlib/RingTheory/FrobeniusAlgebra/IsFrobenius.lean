/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.LinearAlgebra.Coevaluation
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.FrobeniusAlgebra.Basic

/-!
# Frobenius algebras and the Frobenius equations

In this file, we show that a `FrobeniusAlgebra` induces a `Coalgebra`, and that this
coalgebra satisfies the Frobenius equations (`Coalgebra.IsFrobenius`).
See `FrobeniusAlgebra.toCoalgebra` and `FrobeniusAlgebra.isFrobenius_toCoalgebra`.
**Note** that this is not an instance since there can be other non equivalent coalgebras
on your algebra.

We also show that a coalgebra that satisfies the Frobenius equations induces
a natural Frobenius algebra.
-/

open scoped RingTheory.LinearMap
open LinearMap Module TensorProduct

public section

namespace FrobeniusAlgebra
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] [FrobeniusAlgebra K A]

local notation3 "α" => (TensorProduct.assoc K _ _ _).toLinearMap
local notation3 "α⁻¹" => (TensorProduct.assoc K _ _ _).symm.toLinearMap
local notation3 "β" => (TensorProduct.lid K _).toLinearMap
local notation3 "β⁻¹" => (TensorProduct.lid K _).symm.toLinearMap
local notation3 "γ" => (TensorProduct.rid K _).toLinearMap
local notation3 "γ⁻¹" => (TensorProduct.rid K _).symm.toLinearMap
local notation "rT" => rTensor
local notation "lT" => lTensor

variable (K A) in
/-- The natural left-sided comultiplication. -/
noncomputable abbrev comulLeft : A →ₗ[K] A ⊗[K] A :=
  lT A μ[K] ∘ₗ α ∘ₗ rT A (lT A (equivDual K A).symm ∘ₗ coevaluation K A) ∘ₗ β⁻¹

variable (K A) in
/-- The natural right-sided comultiplication. -/
noncomputable abbrev comulRight : A →ₗ[K] A ⊗[K] A :=
  rT A μ[K] ∘ₗ α⁻¹ ∘ₗ lT A (lT A (equivDual K A).symm ∘ₗ coevaluation K A) ∘ₗ γ⁻¹

lemma lTensor_dual_comp_comulLeft_comp_lid :
    lT A dual ∘ₗ comulLeft K A ∘ₗ β = TensorProduct.comm K K A := calc
  _ = lT A (contractLeft K A) ∘ₗ α ∘ₗ rT A (coevaluation K A) := by
    ext; simp [coevaluation_apply_one, sum_tmul, mul'_apply]
  _ = _ := by ext; simp [contractLeft_assoc_coevaluation']

lemma rTensor_comp_comulRight_comp_rid :
    rT A dual ∘ₗ comulRight K A ∘ₗ γ = TensorProduct.comm K A K := calc
  _ = lT K (equivDual K A).symm ∘ₗ
      (rT (Dual K A) (contractLeft K A) ∘ₗ α⁻¹ ∘ₗ lT (Dual K A) (coevaluation K A)) ∘ₗ
      rT K (equivDual K A) := by
    ext; simp [coevaluation_apply_one, tmul_sum, mul'_apply]
  _ = _ := by ext; simp [contractLeft_assoc_coevaluation]

/-- The left-sided and right-sided comultiplication maps are equal. -/
lemma comulLeft_eq_comulRight : comulLeft K A = comulRight K A := by
  obtain ⟨S, hS⟩ := exists_finset ((lT A (equivDual K A).symm.toLinearMap ∘ₗ coevaluation K A) 1)
  ext a
  calc
    _ = ∑ p ∈ S, p.1 ⊗ₜ[K] (p.2 * a) := by simp [hS, sum_tmul]
    _ = ∑ q ∈ S, (∑ p ∈ S, dual (p.2 * (a * q.1)) • p.1) ⊗ₜ[K] q.2 := by
      simp_rw [sum_tmul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr
      · rfl
      intro s hs
      have : ∑ x ∈ S, dual (R := K) (s.2 * a * x.1) • x.2 = s.2 * a := by
        simpa [hS, tmul_sum] using
          congr(β ($rTensor_comp_comulRight_comp_rid ((s.2 * a) ⊗ₜ[K] 1)))
      rw [← this]
      simp [tmul_sum, smul_tmul', mul_assoc]
      rfl
    _ = ∑ q ∈ S, (a * q.1) ⊗ₜ[K] q.2 := by
      have (a : A) : ∑ x ∈ S, dual (R := K) (x.2 * a) • x.1 = a := by
        simpa [hS, tmul_sum, sum_tmul] using
          congr(γ ($lTensor_dual_comp_comulLeft_comp_lid (1 ⊗ₜ[K] a)))
      simp_rw [this]
    _ = _ := by simp [hS, tmul_sum]

variable (K A) in
/-- A Frobenius algebra induces a coalgebra that satisfies the Frobenius equations
(see `isFrobenius_toCoalgebra`).
**Note** that this is not an instance since there can be other non equivalent coalgebras
on your algebra. -/
noncomputable abbrev toCoalgebra : Coalgebra K A where
  comul := comulLeft K A
  counit := dual
  coassoc := by
    ext
    nth_rw 2 3 [comulLeft_eq_comulRight]
    simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      rid_symm_apply, lTensor_tmul, coevaluation_apply_one, tmul_sum, map_sum, assoc_symm_tmul,
      rTensor_tmul, mul'_apply, lid_symm_apply, sum_tmul, assoc_tmul, mul_assoc]
    rw [Finset.sum_comm]
  rTensor_counit_comp_comul := by
    rw [comulLeft_eq_comulRight, ← (TensorProduct.rid K _).eq_comp_toLinearMap_iff, comp_assoc,
      rTensor_comp_comulRight_comp_rid]
    ext; simp
  lTensor_counit_comp_comul := by
    rw [← (TensorProduct.lid K _).eq_comp_toLinearMap_iff, comp_assoc,
      lTensor_dual_comp_comulLeft_comp_lid]
    ext; simp

variable (K A) in
attribute [local instance] toCoalgebra in
/-- The coalgebra coming from a Frobenius algebra satisfies the Frobenius equations. -/
theorem isFrobenius_toCoalgebra : Coalgebra.IsFrobenius K A where
  left_eq_right := by
    simp only [Coalgebra.IsFrobenius.left, Coalgebra.IsFrobenius.right, CoalgebraStruct.comul]
    nth_rw 1 [comulLeft_eq_comulRight]
    ext
    simp [coevaluation_apply_one, tmul_sum, sum_tmul]

open Coalgebra in
/-- A coalgebra that satisfies the Frobenius equations is a Frobenius algebra with the counit
as its dual. -/
abbrev ofIsFrobenius (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A]
    [IsFrobenius R A] : FrobeniusAlgebra R A where
  dual := counit
  bijective_compr₂_mul := IsFrobenius.bijective_compr₂_mul_counit

end FrobeniusAlgebra
