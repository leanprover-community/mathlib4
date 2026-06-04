/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic.Positivity.Finset

/-!
# Direct sum of metric spaces

This files endows the direct sum `ι →₀ X` of `ι`-many copies of a metric space `X` with the
L^1 metric.
-/

public section

namespace Finsupp
variable {ι X : Type*} [Zero X]

/-- The L^1 extended metric on `ι`-many copies of a metric space `X` -/
noncomputable instance [PseudoEMetricSpace X] : PseudoEMetricSpace (ι →₀ X) where
  edist f g := (f.zipWith edist (edist_self _) g).sum fun i r ↦ r
  edist_self f := by simp [sum]
  edist_comm f g := by simp only [sum, zipWith_apply, edist_comm]; congr 1; ext i; simp [edist_comm]
  edist_triangle f g h := calc
    _ ≤ ∑ i ∈ (zipWith edist (edist_self _) f h).support, edist (f i) (g i)
      + ∑ i ∈ (zipWith edist (edist_self _) f h).support, edist (g i) (h i) := by
      rw [← Finset.sum_add_distrib, sum]; gcongr; exact edist_triangle ..
    _ ≤ _ := by
      simp only [sum, zipWith_apply]
      gcongr ?_ + ?_ <;> exact Finset.sum_le_sum_of_ne_zero (by simp)

lemma edist_def [PseudoEMetricSpace X] (f g : ι →₀ X) :
    edist f g = (f.zipWith edist (edist_self _) g).sum fun _i r ↦ r := rfl

/-- The L^1 extended metric on `ι`-many copies of a metric space `X` -/
noncomputable instance [EMetricSpace X] : EMetricSpace (ι →₀ X) where
  eq_of_edist_eq_zero {f g} hfg := by simpa [edist_def, sum, DFunLike.ext_iff] using hfg

/-- The L^1 metric on `ι`-many copies of a metric space `X` -/
noncomputable instance [PseudoMetricSpace X] : PseudoMetricSpace (ι →₀ X) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist
    (fun f g ↦ (f.zipWith dist (dist_self _) g).sum fun i r ↦ r)
    (fun f g ↦ by dsimp [sum]; positivity) fun f g ↦ by
      simp only [edist_def, sum, zipWith_apply, ← coe_nnreal_ennreal_nndist, ← coe_nndist,
        ← ENNReal.ofNNReal_finsetSum, ← NNReal.coe_sum, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inj]
      congr 1
      ext i
      simp [← coe_nndist, ← coe_nnreal_ennreal_nndist]

lemma dist_def [PseudoMetricSpace X] (f g : ι →₀ X) :
    dist f g = (f.zipWith dist (dist_self _) g).sum fun _i r ↦ r := rfl

lemma nndist_def [PseudoMetricSpace X] (f g : ι →₀ X) :
    nndist f g = (f.zipWith nndist (nndist_self _) g).sum fun _i r ↦ r := by
  ext
  simp only [coe_nndist, dist_def, sum, zipWith_apply, NNReal.coe_sum]
  congr 1
  ext i
  simp [← coe_nndist]

/-- The L^1 metric on `ι`-many copies of a metric space `X` -/
noncomputable instance [MetricSpace X] : MetricSpace (ι →₀ X) :=
  EMetricSpace.toMetricSpaceOfDist
    (fun f g ↦ (f.zipWith dist (dist_self _) g).sum fun i r ↦ r)
    (fun f g ↦ by dsimp [sum]; positivity) fun f g ↦ by
      simp only [nndist_def, sum, zipWith_apply, ← coe_nnreal_ennreal_nndist,
        ← coe_nndist, ← NNReal.coe_sum, ENNReal.ofReal_coe_nnreal, ENNReal.coe_inj]
      congr 1
      ext i
      simp [← coe_nndist]

end Finsupp
