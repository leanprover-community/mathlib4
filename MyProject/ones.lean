import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.FiniteDimension

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import Init.Data.Fin.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Analysis.Subadditive

--fkt lemma is fully contained in lean
--and is described by the followinf theorems

#check Subadditive --definition
#check Subadditive.lim
#check Subadditive.tendsto_lim

open MeasureTheory
open ENNReal
open Set
open Function
open scoped BigOperators
open Finset



structure partition {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] :=
  f : ℕ → Set α         -- A function from natural numbers to sets of terms in α
  measurable : ∀ n, MeasurableSet (f n)  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : (⋃ n, f n) = Set.univ)  -- The union of all sets covers the entire space

--defining finite partitions given measure

structure finpart {α : Type*} (m : MeasurableSpace α) (μ : Measure α) [IsProbabilityMeasure μ] (n: ℕ):=
  (f : Fin n → Set α)          -- A function from finite sets of size n to sets of terms in α
  (measurable : ∀ i : Fin n, MeasurableSet (f i))  -- Each set is measurable
  (disjoint : ∀ i j, i ≠ j → μ (f i ∩ f j) = 0)  -- The sets are pairwise disjoint
  (cover : (⋃ i, f i) = Set.univ)  -- The union of all sets covers the entire space

def finpart_to_partition {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (n : ℕ) (fp : finpart m μ n) : partition m μ
    where
  f := λ k ↦ if h : k < n then fp.f ⟨k, h⟩ else ∅
  measurable:= by
    intro k; by_cases h : k<n
    · simp only [dif_pos h]
      exact fp.measurable ⟨k, h⟩
    · simp only [dif_neg h]
      exact MeasurableSet.empty
  disjoint:=  by
    intro i j hij
    by_cases hi : i < n
    · by_cases hj: j < n
      · simp only [dif_pos hi, dif_pos hj]
        exact fp.disjoint ⟨i, hi⟩ ⟨j, hj⟩ (λ h ↦ hij (Fin.val_eq_of_eq h))
      · simp only [dif_pos hi, dif_neg hj, Set.inter_empty, measure_empty]
    · simp only [dif_neg hi, Set.empty_inter, measure_empty]
  cover:= by
    ext x
    constructor
    · tauto
    · intro h;dsimp; rw[← fp.cover] at h; rcases mem_iUnion.mp h with ⟨a, ha⟩
      rw[mem_iUnion]
      use a; simp only [dif_pos a.is_lt]; exact ha

#check tsum_eq_sum
#check Finset_
#check Finset.sum_congr

theorem  sumeq {α : Type*} {m : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ]
  (n : ℕ) (fp : finpart m μ n):
  (∑ n', (μ (fp.f n')).toReal)= ∑' n', (μ ((finpart_to_partition n fp).f n')).toReal := by
  let s : Finset ℕ := Finset.range n
  have h: ∑' n', (μ ((finpart_to_partition n fp).f n')).toReal = ∑ n' ∈ s, ((μ ((finpart_to_partition n fp).f n')).toReal) := by
    apply tsum_eq_sum
    intro b hb
    have hbn : b ≥ n := by
      simp[ Finset.mem_range]
      sorry
    sorry

  rw[h]
  simp only [finpart_to_partition, dif_pos]
  apply Finset.sum_congr

  congr
  · ext hx





  apply?


theorem finset_univ_fin_eq_range {n : ℕ} : (Finset.univ : Finset (Fin n)).image (λ x ↦ (x : ℕ)) = Finset.range n :=
begin
