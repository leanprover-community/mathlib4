/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.OrderClosed

/-!
# Natural density

We define the density of a set `A` along a `SummationFilter` as the limit of the proportion of
elements of `A` in the finite sets of the filter. Natural density is the specialization to the
conditional summation filter on the natural numbers. Thus, a set `A` of natural numbers has
natural density `δ` when

$$
\lim_{n \to \infty} \frac{|A \cap \{0, \ldots, n - 1\}|}{n} = \delta.
$$

This is captured by the predicates `Set.HasDensity A δ L` and `Set.HasNaturalDensity A δ`, and by
the definition `Set.naturalDensity A`, the natural density as a real number (with junk value `0`
when it does not exist).

## Main results

* `Set.hasNaturalDensity_iff` characterizes natural density using `Finset.range`.
* `Set.hasNaturalDensity_empty` and `Set.hasNaturalDensity_univ` compute the natural densities of
  the empty and universal sets.
* `Set.HasDensity.nonneg` and `Set.HasDensity.le_one` show that a density along a nontrivial
  summation filter lies in the interval `[0, 1]`.

-/

public section

open Filter Finset SummationFilter Topology

namespace Set

variable {α : Type*}

open scoped Classical in
/-- A set `A` has density `δ` along a summation filter `L` if the proportions of elements of `A`
in the finite sets tend to `δ` along `L`. -/
def HasDensity (A : Set α) (δ : ℝ) (L : SummationFilter α) : Prop :=
  Tendsto (fun s : Finset α ↦ ((s.filter (· ∈ A)).card : ℝ) / s.card) L.filter (𝓝 δ)

/-- A set of natural numbers has natural density `δ` if it has density `δ` along the conditional
summation filter on `ℕ`. -/
def HasNaturalDensity (A : Set ℕ) (δ : ℝ) : Prop :=
  HasDensity A δ (SummationFilter.conditional ℕ)

section Density

variable {A : Set α} {L : SummationFilter α}

/-- Density along a nontrivial summation filter, when it exists, is unique. -/
theorem HasDensity.unique [L.NeBot] {δ ε : ℝ} (hδ : A.HasDensity δ L)
    (hε : A.HasDensity ε L) : δ = ε :=
  tendsto_nhds_unique hδ hε

/-- The empty set has density `0` along every summation filter. -/
theorem hasDensity_empty (L : SummationFilter α) : HasDensity (∅ : Set α) 0 L := by
  classical
  rw [HasDensity]
  simpa using (tendsto_const_nhds :
    Tendsto (fun _ : Finset α ↦ (0 : ℝ)) L.filter (𝓝 0))

/-- A density along a nontrivial summation filter is nonnegative. -/
theorem HasDensity.nonneg [L.NeBot] {δ : ℝ} (h : A.HasDensity δ L) : 0 ≤ δ := by
  rw [HasDensity] at h
  exact ge_of_tendsto h <| Eventually.of_forall fun _ ↦ by positivity

/-- A density along a nontrivial summation filter is at most `1`. -/
theorem HasDensity.le_one [L.NeBot] {δ : ℝ} (h : A.HasDensity δ L) : δ ≤ 1 := by
  classical
  rw [HasDensity] at h
  refine le_of_tendsto h <| Eventually.of_forall fun s ↦ ?_
  by_cases hs : s.card = 0
  · simp [hs]
  rw [div_le_one (Nat.cast_pos.2 (Nat.pos_of_ne_zero hs))]
  exact_mod_cast card_filter_le s fun a ↦ a ∈ A

end Density

section NaturalDensity

variable {A : Set ℕ}

open scoped Classical in
/-- A set `A` has natural density `δ` if and only if its proportions in `Finset.range n` tend to
`δ` as `n` tends to infinity. -/
theorem hasNaturalDensity_iff {δ : ℝ} :
    A.HasNaturalDensity δ ↔
      Tendsto (fun n : ℕ ↦ (((Finset.range n).filter (· ∈ A)).card : ℝ) / n) atTop (𝓝 δ) := by
  rw [HasNaturalDensity, HasDensity, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  simp [Function.comp_def]

open scoped Classical in
/-- The natural density of `A` as a real number, taking the junk value `0` when `A` has no
natural density. -/
noncomputable def naturalDensity (A : Set ℕ) : ℝ :=
  if h : ∃ δ, A.HasNaturalDensity δ then h.choose else 0

/-- Natural density, when it exists, is unique. -/
theorem HasNaturalDensity.unique {δ ε : ℝ} (hδ : A.HasNaturalDensity δ)
    (hε : A.HasNaturalDensity ε) : δ = ε :=
  HasDensity.unique hδ hε

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
theorem hasNaturalDensity_empty : HasNaturalDensity (∅ : Set ℕ) 0 :=
  hasDensity_empty _

/-- The universal set has natural density `1`. -/
theorem hasNaturalDensity_univ : HasNaturalDensity (Set.univ : Set ℕ) 1 := by
  classical
  rw [hasNaturalDensity_iff]
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
theorem HasNaturalDensity.nonneg {δ : ℝ} (h : A.HasNaturalDensity δ) : 0 ≤ δ :=
  HasDensity.nonneg h

/-- A natural density is at most `1`. -/
theorem HasNaturalDensity.le_one {δ : ℝ} (h : A.HasNaturalDensity δ) : δ ≤ 1 :=
  HasDensity.le_one h

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

end NaturalDensity

end Set
