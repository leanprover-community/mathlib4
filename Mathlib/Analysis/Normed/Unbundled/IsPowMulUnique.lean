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

section foo

theorem one_le_map_one {F α β : Type*}
    [Ring α] [Nontrivial α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
    [FunLike F α β] [RingNormClass F α β] (f : F) :
    1 ≤ f 1 := by
  simpa [map_pos_of_ne_zero f one_ne_zero] using map_mul_le_mul f 1 1

@[to_additive]
theorem Finset.map_prod_le_prod {F α β ι : Type*} [CommMonoid α] [CommMonoid β] [Preorder β]
    [IsOrderedMonoid β]
    [FunLike F α β]
    [SubmultiplicativeHomClass F α β] [OneHomClass F α β] (f : F) (s : Finset ι) (c : ι → α) :
    f (∏ i ∈ s, c i) ≤ ∏ i ∈ s, f (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => grw [Finset.prod_insert his, Finset.prod_insert his, map_mul_le_mul, ih]

variable {A B : Type*} [SeminormedCommRing A] [Ring B] [Algebra A B]

/-- A power-multiplicative norm on an algebraic extension of a trivially normed field is trivial. -/
theorem AlgebraNorm.le_one_of_trivial (hK : ∀ x : A, ‖x‖ ≤ 1)
    (f : AlgebraNorm A B) (hf : IsPowMul f) (x : B) (hx : IsIntegral A x) : f x ≤ 1 := by
  let S := Algebra.adjoin A {x}
  obtain ⟨s, hs⟩ : S.toSubmodule.FG := hx.fg_adjoin_singleton
  have h n (hn : 1 ≤ n) : f x ^ n ≤ ∑ a : s, f a := by
    obtain ⟨c, hc⟩ : ∃ c : s → A, ∑ a : s, c a • a.val = x ^ n := by
      rw [← Submodule.mem_span_finset', hs]
      exact S.pow_mem (Algebra.self_mem_adjoin_singleton A x) n
    grw [← hf x hn, ← hc, Finset.map_sum_le_sum]
    simp_rw [map_smul_eq_mul]
    grw [hK]
    simp
  contrapose! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (∑ a : s, f a) h
  by_cases! hn0 : n = 0
  · exact ⟨1, le_rfl, by grw [pow_one, hn, hn0, pow_zero, h]⟩
  · exact ⟨n, hn0.pos, hn⟩

variable {K L : Type*} [SeminormedCommRing K] [DivisionRing L] [Algebra K L]
  [Algebra.IsIntegral K L]

/-- A power-multiplicative norm on an algebraic extension of a trivially normed field is trivial. -/
theorem AlgebraNorm.eq_one_of_trivial
    (hK : ∀ x : K, ‖x‖ ≤ 1) (f : AlgebraNorm K L) (hf : IsPowMul f)
    (x : L) (hx : x ≠ 0) : f x = 1 := by
  refine le_antisymm (AlgebraNorm.le_one_of_trivial hK f hf x (Algebra.IsIntegral.isIntegral x)) ?_
  grw [one_le_map_one f, ← inv_mul_cancel₀ hx, map_mul_le_mul, f.le_one_of_trivial hK hf, one_mul]
  exact Algebra.IsIntegral.isIntegral x⁻¹

end foo

open IntermediateField

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

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
  by_cases! hK : ∀ x : K, ‖x‖ ≤ 1
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [f.eq_one_of_trivial hK hf_pm x hx, g.eq_one_of_trivial hK hg_pm x hx]
  · let : NontriviallyNormedField K := ⟨hK⟩
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
