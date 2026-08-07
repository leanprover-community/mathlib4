/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-!
# Natural density

We define the natural density of a set `A` of natural numbers as the limit

$$
\lim_{n \to \infty} \frac{|A \cap \{1, \ldots, n\}|}{n},
$$

when this limit exists.

This is captured by the predicate `Set.HasNaturalDensity A δ`, stating that the finite-prefix
ratios tend to `δ`, and by the definition `Set.naturalDensity A`, the density as a real number
(with junk value `0` when it does not exist).

## Main results

* `Set.hasNaturalDensity_empty` and `Set.hasNaturalDensity_univ` compute the densities of the
  empty and universal sets.
* `Set.HasNaturalDensity.nonneg` and `Set.HasNaturalDensity.le_one` show that a natural density
  lies in the interval `[0, 1]`.

-/

public section

open Filter Finset Topology

namespace Set

open scoped Classical in
/-- A set `A` of natural numbers has natural density `δ` if
`|A ∩ {1, ..., n}| / n` tends to `δ` as `n` tends to infinity. -/
def HasNaturalDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun n : ℕ ↦ (((Finset.Ioc 0 n).filter (· ∈ A)).card : ℝ) / n) atTop (𝓝 δ)

open scoped Classical in
/-- The natural density of `A` as a real number, taking the junk value `0` when `A` has no
natural density. -/
noncomputable def naturalDensity (A : Set ℕ) : ℝ :=
  if h : ∃ δ, A.HasNaturalDensity δ then h.choose else 0

variable {A : Set ℕ}

/-- Natural density, when it exists, is unique. -/
theorem HasNaturalDensity.unique {δ ε : ℝ} (hδ : A.HasNaturalDensity δ)
    (hε : A.HasNaturalDensity ε) : δ = ε :=
  tendsto_nhds_unique hδ hε

/-- If `A` has no natural density, then `naturalDensity A = 0`. -/
theorem naturalDensity_eq_zero_of_not_hasNaturalDensity
    (h : ∀ δ, ¬ A.HasNaturalDensity δ) : A.naturalDensity = 0 := by
  rw [naturalDensity, dif_neg (not_exists.mpr h)]

/-- If `A` has natural density `δ`, then `naturalDensity A = δ`. -/
theorem HasNaturalDensity.naturalDensity_eq {δ : ℝ} (h : A.HasNaturalDensity δ) :
    A.naturalDensity = δ := by
  rw [naturalDensity, dif_pos ⟨δ, h⟩]
  exact (Exists.choose_spec ⟨δ, h⟩).unique h

/-- The empty set has natural density `0`. -/
theorem hasNaturalDensity_empty : HasNaturalDensity (∅ : Set ℕ) 0 := by
  simp [HasNaturalDensity]

/-- The universal set has natural density `1`. -/
theorem hasNaturalDensity_univ : HasNaturalDensity (Set.univ : Set ℕ) 1 := by
  rw [HasNaturalDensity]
  refine tendsto_const_nhds.congr' ?_
  exact eventually_atTop.2 ⟨1, fun n hn ↦ by
    have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn)
    simp [hn0]⟩

/-- The natural density of the empty set is `0`. -/
@[simp]
theorem naturalDensity_empty : naturalDensity (∅ : Set ℕ) = 0 :=
  hasNaturalDensity_empty.naturalDensity_eq

/-- The natural density of the universal set is `1`. -/
@[simp]
theorem naturalDensity_univ : naturalDensity (Set.univ : Set ℕ) = 1 :=
  hasNaturalDensity_univ.naturalDensity_eq

/-- A natural density is nonnegative. -/
theorem HasNaturalDensity.nonneg {δ : ℝ} (h : A.HasNaturalDensity δ) : 0 ≤ δ := by
  rw [HasNaturalDensity] at h
  exact ge_of_tendsto h <| Eventually.of_forall fun _ ↦ by positivity

/-- A natural density is at most `1`. -/
theorem HasNaturalDensity.le_one {δ : ℝ} (h : A.HasNaturalDensity δ) : δ ≤ 1 := by
  classical
  rw [HasNaturalDensity] at h
  refine le_of_tendsto h <| Eventually.of_forall fun n ↦ ?_
  by_cases hn : n = 0
  · simp [hn]
  rw [div_le_one (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))]
  exact_mod_cast (card_filter_le (Finset.Ioc 0 n) fun a ↦ a ∈ A).trans_eq (by simp)

variable (A) in
/-- The natural density is nonnegative. -/
theorem naturalDensity_nonneg : 0 ≤ A.naturalDensity := by
  rw [naturalDensity]
  split_ifs with h
  · exact h.choose_spec.nonneg
  · exact le_rfl

variable (A) in
/-- The natural density is at most `1`. -/
theorem naturalDensity_le_one : A.naturalDensity ≤ 1 := by
  rw [naturalDensity]
  split_ifs with h
  · exact h.choose_spec.le_one
  · exact zero_le_one

end Set
