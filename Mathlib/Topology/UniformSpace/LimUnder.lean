/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Int.Interval
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Arithmetic of limUnder functions

This file provides some lemmas about arithmetic of `limUnder` functions, such as how it behaves
with respect to addition, multiplication, scalar multiplication, negation and subtraction.

-/

open Filter

variable {X Z α : Type*} [UniformSpace X] [CompleteSpace X]
    [T2Space X] [Preorder α] [(atTop : Filter α).NeBot]

@[to_additive]
lemma limUnder.mul [Group X] [IsUniformGroup X] {f g : α → X} (hf : CauchySeq f)
    (hg : CauchySeq g) : (limUnder atTop f) * (limUnder atTop g) = limUnder atTop (f * g) := by
  nth_rw 3 [Tendsto.limUnder_eq]
  exact Tendsto.mul (hf.tendsto_limUnder) (hg.tendsto_limUnder)

lemma limUnder.smul_const {Y : Type*} [Nonempty X] [SMul Y X] [ContinuousConstSMul Y X]
    (f : α → X) (hf : CauchySeq f) (c : Y) : c • (limUnder atTop f)= limUnder atTop (c • f) := by
  nth_rw 2 [Tendsto.limUnder_eq]
  exact Tendsto.const_smul hf.tendsto_limUnder c

lemma limUnder.mul_const {f : α → X} [Monoid X] [ContinuousMul X] (hf : CauchySeq f) (c : X) :
    c * (limUnder atTop f) = limUnder atTop (c • f) := by
  nth_rw 2 [Tendsto.limUnder_eq]
  exact Tendsto.const_mul c (CauchySeq.tendsto_limUnder hf)

lemma limUnder.neg {f : α → X} [Nonempty X] [Neg X] [ContinuousNeg X] (hf : CauchySeq f) :
    -(limUnder atTop f) = limUnder atTop (-f) := by
  nth_rw 2 [Tendsto.limUnder_eq]
  exact Tendsto.neg (CauchySeq.tendsto_limUnder hf)

lemma limUnder.sub [AddGroup X] [IsUniformAddGroup X] (f g : α → X) (hf : CauchySeq f)
    (hg : CauchySeq g) : (limUnder atTop f) - (limUnder atTop g) = limUnder atTop (f - g) := by
  nth_rw 3 [Tendsto.limUnder_eq]
  exact Tendsto.sub (hf.tendsto_limUnder) (hg.tendsto_limUnder)

lemma limUnder_congr_eventually [Nonempty X] (f g : α → X) (h : ∀ᶠ n in atTop, f n = g n)
  (hf : CauchySeq f) (hg : CauchySeq g) : limUnder atTop f = limUnder atTop g := by
  rw [Tendsto.limUnder_eq (x := (limUnder atTop f)) hf.tendsto_limUnder, Tendsto.limUnder_eq ]
  exact Tendsto.congr' (EventuallyEq.symm h) (hg.tendsto_limUnder)

section InfiniteSums

lemma tendsto_Icc_atTop_atTop : Tendsto (fun N : ℕ => Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma tendsto_Ico_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    Int.lt_add_one_iff.mpr (le_abs_self x)⟩ ⟩

lemma tendsto_Ioc_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ioc (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioc_subset_Ioc (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x)).le⟩⟩

lemma tendsto_Ioo_atTop_atTop : Tendsto (fun N : ℕ => Finset.Ioo (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ioo_subset_Ioo (by omega) (by gcongr))
  exact fun x => ⟨x.natAbs + 1, by simpa using ⟨by apply le_trans _ (add_abs_nonneg x); omega,
    (Int.lt_add_one_iff.mpr (le_abs_self x))⟩⟩

variable {Y : Type*} [AddCommMonoid Y] [TopologicalSpace Y] [T2Space Y] {f : ℤ → Y}

lemma int_tsum_limUnder_Icc_atTop (hf : Summable f) :
    ∑' n, f n = limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Icc (-N : ℤ) N, f n) := by
  rw [Tendsto.limUnder_eq]
  exact (hf.hasSum).comp tendsto_Icc_atTop_atTop

lemma int_tsum_limUnder_Ico_atTop (hf : Summable f) :
    ∑' n, f n = limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Ico (-N : ℤ) N, f n) := by
  rw [Tendsto.limUnder_eq]
  exact (hf.hasSum).comp tendsto_Ico_atTop_atTop

lemma int_tsum_limUnder_Ioc_atTop (hf : Summable f) :
    ∑' n, f n = limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Ioc (-N : ℤ) N, f n) := by
  rw [Tendsto.limUnder_eq]
  exact (hf.hasSum).comp tendsto_Ioc_atTop_atTop

lemma int_tsum_limUnder_Ioo_atTop (hf : Summable f) :
    ∑' n, f n = limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Ioo (-N : ℤ) N, f n) := by
  rw [Tendsto.limUnder_eq]
  exact (hf.hasSum).comp tendsto_Ioo_atTop_atTop

end InfiniteSums
