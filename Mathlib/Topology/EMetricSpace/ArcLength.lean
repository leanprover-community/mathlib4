/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Success Moses, Zhenhua Wu
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Arc length of curves

This file defines the arc length of a curve in a `WeakPseudoEMetricSpace` as the variation of the
curve on an interval `Set.Icc a b`, and develops a basic API for this definition.

## Main declarations

* `arcLength`: the arc length of a curve (image of a linear order) on a closed interval.
* `arcLength_eq_zero_of_le`: arc length vanishes on a reversed interval.
* `arcLength_self`: arc length vanishes on a degenerate interval.
* `edist_le_arcLength`: the endpoint distance is bounded above by the arc length.
* `arcLength_add`: arc length is additive on adjacent intervals.
* `arcLength_sum`: the arc lengths along a monotone subdivision sum to the whole arc length.
* `arcLength_comp_eq_of_monotoneOn`: arc length is preserved by monotone reparametrizations.
* `arcLength_comp_eq_of_antitoneOn`: arc length is preserved by antitone reparametrizations.
-/

open scoped ENNReal
open Set

@[expose] public noncomputable section

variable {α E : Type*} [LinearOrder α] [TopologicalSpace E] [WeakPseudoEMetricSpace E]
  (f : α → E) {a b c : α}

/-- The arc length of `f` on `[a, b]` is the variation of `f` on the interval `Set.Icc a b`.
This quantity is zero when `b ≤ a`. -/
noncomputable def arcLength (a b : α) : ℝ≥0∞ :=
  eVariationOn f (Set.Icc a b)

/-- The arc length on `[a, b]` vanishes when `b ≤ a`. -/
theorem arcLength_eq_zero_of_le (hba : b ≤ a) : arcLength f a b = 0 :=
  eVariationOn.subsingleton f <| by simp [hba]

/-- The arc length on the degenerate interval `[a, a]` is zero. -/
theorem arcLength_self (a : α) : arcLength f a a = 0 := arcLength_eq_zero_of_le _ le_rfl

/-- The endpoint distance on `[a, b]` is bounded above by the arc length. -/
theorem edist_le_arcLength (hab : a ≤ b) : edist (f a) (f b) ≤ arcLength f a b := by
  refine eVariationOn.edist_le f ?_ ?_ <;> simp [hab]

/-- Arc length is additive on adjacent intervals. -/
theorem arcLength_add (hab : a ≤ b) (hbc : b ≤ c) :
    arcLength f a b + arcLength f b c = arcLength f a c := by
  simp_rw [arcLength]
  convert eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (by simp) <;> simp

/-- The arc length along a monotone finite subdivision equals the arc length of the whole
interval. -/
theorem arcLength_sum {n : ℕ} {u : ℕ → α} (hu : Monotone u) :
    ∑ i ∈ Finset.range n, arcLength f (u i) (u (i + 1)) = arcLength f (u 0) (u n) := by
  induction n with
  | zero => rw [arcLength_self, Finset.sum_range_zero]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, arcLength_add f (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]

/-- Arc length is preserved by a monotone reparametrization whose image is exactly the target
interval. -/
theorem arcLength_comp_eq_of_monotoneOn {β : Type*} [LinearOrder β] {a b : β} (g : β → α)
    (hg : MonotoneOn g (Set.Icc a b)) (himage : g '' Set.Icc a b = Set.Icc (g a) (g b)) :
    arcLength (f ∘ g) a b = arcLength f (g a) (g b) := by
  rw [arcLength, arcLength, eVariationOn.comp_eq_of_monotoneOn _ _ hg, himage]

/-- Arc length is preserved by an antitone reparametrization whose image is exactly the target
interval, with reversed endpoints. -/
theorem arcLength_comp_eq_of_antitoneOn {β : Type*} [LinearOrder β] {a b : β} (g : β → α)
    (hg : AntitoneOn g (Set.Icc a b)) (himage : g '' Set.Icc a b = Set.Icc (g b) (g a)) :
    arcLength (f ∘ g) a b = arcLength f (g b) (g a) := by
  rw [arcLength, arcLength, eVariationOn.comp_eq_of_antitoneOn _ _ hg, himage]

end
