/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson, Newell Jensen
-/
import Mathlib.Topology.MetricSpace.Infsep

/-!
# Well-spaced point sets.

This file defines point sets that are *well-spaced*.

## Main definitions

* `Set.isPacking`: ε-packings.
* `Set.isCovering`: ε-coverings.
* `Set.isNet`: ε-nets.
* `Set.uniformlyDiscrete`: Uniformly discrete point sets.
* `Set.relativelyDense`: Relatively dense point sets.
* `Set.Delone`: Delone point sets.
* `Set.Meyer`: Meyer point sets.

!-/


universe u

variable {α β : Type*}

open scoped ENNReal

class DiscreteDist (α : Type u) [Dist α] : Type u where
  exists_pos_lt_dist : ∃ r > 0, ∀ x y : α, x ≠ y → r < dist x y

class BoundedDist (α : Type u) [Dist α] : Type u where
  exists_finite_dist_lt : ∃ R : ℝ, ∀ x y : α, dist x y < R

class DiscreteEDist (α : Type u) [EDist α] : Type u where
  exists_pos_lt_edist : ∃ r > 0, ∀ x y : α, x ≠ y → r < edist x y

class BoundedEDist (α : Type u) [EDist α] : Type u where
  exists_finite_edist_lt : ∃ R : ℝ≥0∞, R < ∞ ∧ ∀ x y : α, edist x y < R

instance [PseudoMetricSpace α] [DiscreteDist α] : DiscreteEDist α where
  exists_pos_lt_edist := by
    rcases DiscreteDist.exists_pos_lt_dist (α := α) with ⟨r, r_pos, hr⟩
    use ENNReal.ofReal r
    simp_rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff_of_nonneg r_pos.le, ENNReal.ofReal_pos]
    exact ⟨r_pos, hr⟩

instance [PseudoMetricSpace α] [BoundedDist α] : BoundedEDist α where
  exists_finite_edist_lt := by
    rcases BoundedDist.exists_finite_dist_lt (α := α) with ⟨R, hr⟩
    use ENNReal.ofReal R
    simp_rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff', ENNReal.ofReal_lt_top, true_and, forall_and]
    exact ⟨hr, fun x y => (dist_nonneg).trans_lt (hr x y)⟩

namespace Set

variable [PseudoEMetricSpace α]

/-- The packing radius is half of the smallest distance between distinct members of `s`. -/
noncomputable def packingRadius (s : Set α) : ℝ≥0∞ :=
  sSup fun r => s.PairwiseDisjoint (EMetric.ball · r)

lemma packingRadius_eq_half_einfsep (s : Set α) : s.packingRadius = s.einfsep / 2 := sorry

/-- The covering radius is the smallest distance such that every point of `s` is within this
distance of at least one point in `s`. -/
noncomputable def coveringRadius (s : Set α) : ℝ≥0∞ :=
  sInf fun r => (EMetric.closedBall . r) '' s = univ

-- lemma coveringRadius_eq_something (infEDist? something not defined which should be?)

/-- An ε-packing is a set with packing radius ≥ ε / 2. -/
def isPacking (s : Set α) (ε : ℝ≥0∞) := ε ≤ 2 * (s.packingRadius)

/-- An ε-covering is a set with covering radius ≤ ε. -/
def isCovering (s : Set α) (ε : ℝ≥0∞) := s.coveringRadius ≤ ε

/-- An ε-net is a set that is both an ε-packing and an ε-covering. -/
def isNet (s : Set α) (e : ℝ≥0∞) := s.isPacking e ∧ s.isCovering e

/-- A set is uniformly discrete if it has a nonzero packing radius. -/
def uniformlyDiscrete (s : Set α) := 0 < s.packingRadius

/-- A set is relatively dense if it has a finite covering radius. -/
def relativelyDense (s : Set α) := s.coveringRadius < ∞

/-- A set that is uniformly discrete and relatively dense is a Delone set. -/
def Delone (s : Set α) := s.uniformlyDiscrete ∧ s.relativelyDense

lemma uniformlyDiscrete_of_isPacking_pos (s : Set α) (e : ℝ≥0∞) (e_pos : 0 < e)
    (h : s.isPacking e) : s.uniformlyDiscrete := (ENNReal.mul_pos_iff.mp (h.trans_lt' e_pos)).2

lemma relativelyDense_of_isCovering_finite (s : Set α) (e : ℝ≥0∞) (e_finite : e < ∞)
    (h : s.isCovering e) : s.relativelyDense := h.trans_lt e_finite

lemma delone_of_isNet_pos_finite (s : Set α) (e : ℝ≥0∞) (e_pos : 0 < e) (e_finite : e < ∞)
    (h : s.isNet e) : s.Delone :=
  ⟨s.uniformlyDiscrete_of_isPacking_pos _ e_pos h.1,
  s.relativelyDense_of_isCovering_finite _ e_finite h.2⟩

open scoped Pointwise

/-- A set that is relatively dense and `s - s` is uniformly discerete is a Meyer set. -/
def Meyer (s : Set α) [Sub α] := s.relativelyDense ∧ (s - s).uniformlyDiscrete

end Set
