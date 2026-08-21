/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Unbundled.IsPowMulFaithful
public import Mathlib.Analysis.Normed.Unbundled.SeminormFromConst
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Uniqueness of power-multiplicative norms

In this file, we prove uniqueness of power-multiplicative norms over complete normed fields.

## Main Results

* `IsPowMul.unique` : uniqueness of power-multiplicative norms over complete normed fields.
-/

open IntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

def AlgebraNorm.copy (_f : AlgebraNorm K L) (x : L) : Type _ := K⟮x⟯
deriving Field, Algebra K

instance (f : AlgebraNorm K L) (x : L) : FiniteDimensional K (f.copy x) :=
  adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)

instance (f : AlgebraNorm K L) (x : L) : Algebra (f.copy x) L :=
  inferInstanceAs (Algebra K⟮x⟯ L)

def AlgebraNorm.ringNorm (f : AlgebraNorm K L) (x : L) : RingNorm (f.copy x) where
  toFun y := f ((algebraMap (f.copy x) L) y)
  map_zero' := map_zero _
  add_le' a b := map_add_le_add _ _ _
  neg' y := by simp
  mul_le' a b := map_mul_le_mul _ _ _
  eq_zero_of_map_eq_zero' a ha := by rwa [map_eq_zero_iff_eq_zero, map_eq_zero] at ha

instance (f : AlgebraNorm K L) (x : L) : NormedRing (f.copy x) :=
  (f.ringNorm x).toNormedRing

instance (f : AlgebraNorm K L) (x : L) : NormedAlgebra K (f.copy x) where
  norm_smul_le c y := (map_smul_eq_mul f c (algebraMap (f.copy x) L y)).le

/-- Uniqueness of power-multiplicative norms over complete normed fields. -/
public theorem IsPowMul.unique [CompleteSpace K] {f g : AlgebraNorm K L}
    (hf_pm : IsPowMul f) (hg_pm : IsPowMul g) : f = g := by
  apply eq_of_powMul_faithful f hf_pm g hg_pm
  intro x
  let T₀ : g.copy x ≃ₗ[K] f.copy x := LinearEquiv.refl K K⟮x⟯
  let T : g.copy x ≃L[K] f.copy x := T₀.toContinuousLinearEquiv
  obtain ⟨C1, hC1_pos, hC1⟩ := T.symm.toContinuousLinearMap.isBoundedLinearMap.bound
  obtain ⟨C2, hC2_pos, hC2⟩ := T.toContinuousLinearMap.isBoundedLinearMap.bound
  exact ⟨ C2, C1, hC2_pos, hC1_pos,
    forall_and.mpr ⟨fun y ↦ hC2 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩,
      fun y ↦ hC1 ⟨y, (IntermediateField.algebra_adjoin_le_adjoin K _) y.2⟩⟩⟩

/-- A power-multiplicative algebra norm over a complete normed field is multiplicative. -/
@[expose]
public def AlgebraNorm.toMulAlgebraNorm [CompleteSpace K] (f : AlgebraNorm K L)
    (hf : IsPowMul f) : MulAlgebraNorm K L where
  __ := f
  map_one' := by simpa [map_ne_zero_iff_ne_zero, sq] using hf 1 one_le_two
  map_mul' x y := by
    by_cases hx : f x = 0
    · simp [eq_zero_of_map_eq_zero f hx]
    · let g : AlgebraNorm K L := algebraNormFromConst hx hf
      have hg : IsPowMul g := seminormFromConst_isPowMul hx hf
      rw [hf.unique hg]
      exact seminormFromConst_const_mul hx hf y
