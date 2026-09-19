/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.LiminfLimsup

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotic density

For a set `S` in an order whose lower intervals are finite, `Set.partialDensity S A b` is the
proportion of the elements of a reference set `A` below `b` that belong to `S`. The reference set
defaults to `Set.univ`.

The same finite profile defines relative upper density, relative lower density, and exact relative
density. Ordinary natural density is the specialization to subsets of `ℕ` with reference set
`Set.univ`.

For `S ⊆ ℕ`, its partial natural density is

$$
d_n(S) = \frac{|S \cap \{0, \ldots, n - 1\}|}{n}.
$$

## Main definitions

* `Set.partialDensity`: the finite relative-density profile;
* `Set.upperDensity` and `Set.lowerDensity`: the limsup and liminf of that profile;
* `Set.HasDensity`: convergence of the relative-density profile;
* `Set.HasNaturalDensity`: ordinary natural density on `ℕ`.

## Main results

* `Set.lowerDensity_nonneg`, `Set.lowerDensity_le_upperDensity`, and
  `Set.upperDensity_le_one` bound lower and upper density in `[0, 1]`.
* `Set.hasDensity_univ` gives relative density one when the reference denominator is eventually
  positive.
* `Set.Finite.hasNaturalDensity_zero` shows that finite subsets of `ℕ` have density zero.

The denominator is allowed to vanish. As usual for division in `ℝ`, the corresponding partial
density is then `0`.

There is deliberately no total exact-density value. The always-defined values are `lowerDensity`
and `upperDensity`; `HasDensity` records when the finite profile actually converges.

## Implementation notes

The relative partial-density interface is informed by the experimental
[`FormalConjecturesForMathlib` density module](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjecturesForMathlib/Data/Set/Density.lean).
The definitions and proofs here are adapted independently to current mathlib and use `Finset.Iio`,
without project-local dependencies.

For `S : Set ℕ`, ordinary lower and upper density, relative to `Set.univ`, agree with the linear
growth of the counting function `n ↦ #{x ∈ Finset.range n | x ∈ S}`. Relative density with a general
reference set `A` instead normalizes by `#{x ∈ Finset.range n | x ∈ A}`. The opt-in module
`Mathlib.Combinatorics.AsymptoticDensity.LinearGrowth` provides the ordinary-density bridge without
adding the extended-real growth API to this module's imports.
`Mathlib.Analysis.Asymptotics.ExpGrowth` uses the different normalization `log (u n) / n`, so it is
parallel infrastructure rather than the basis of the present definitions.

## TODO

* Characterize exact density by equality of lower and upper density under the appropriate
  nontriviality hypotheses.
* Develop complement duality, invariance under finite modifications, and finite additivity for
  disjoint sets; state union and intersection results with their necessary existence hypotheses.
* Prove invariance and scaling results for translations, dilations, and suitable order maps.
* Add positive-density, logarithmic-density, and two-sided variants in separate modules.
* Consider other sampling schemes only when concrete applications justify the additional
  abstraction.
-/

@[expose] public section

open Filter Finset Topology

namespace Set

/-- The proportion of elements of `A` below `b` that belong to `S`.

If `A` has no elements below `b`, this is `0` by the convention for division in `ℝ`. -/
noncomputable def partialDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) (b : α) : ℝ :=
  open scoped Classical in
  #{x ∈ Finset.Iio b | x ∈ S ∩ A} / #{x ∈ Finset.Iio b | x ∈ A}

/-- The upper asymptotic density of `S` relative to `A`. -/
noncomputable def upperDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) : ℝ :=
  atTop.limsup (S.partialDensity A)

/-- The lower asymptotic density of `S` relative to `A`. -/
noncomputable def lowerDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (A : Set α := Set.univ) : ℝ :=
  atTop.liminf (S.partialDensity A)

/-- A set `S` has asymptotic density `δ` relative to `A` if its relative partial densities tend to
`δ`. -/
def HasDensity {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
    (S : Set α) (δ : ℝ) (A : Set α := Set.univ) : Prop :=
  Tendsto (S.partialDensity A) atTop (𝓝 δ)

/-- A set of natural numbers has natural density `δ` if its density relative to all natural
numbers is `δ`. -/
def HasNaturalDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  S.HasDensity δ

section PartialDensity

variable {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]

/-- A partial density is nonnegative. -/
theorem partialDensity_nonneg (S A : Set α) (b : α) : 0 ≤ S.partialDensity A b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- A partial density is at most `1`. -/
theorem partialDensity_le_one (S A : Set α) (b : α) : S.partialDensity A b ≤ 1 := by
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
  norm_cast
  exact Finset.card_le_card fun x hx ↦ by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.2⟩

@[simp]
theorem partialDensity_empty (A : Set α) (b : α) : (∅ : Set α).partialDensity A b = 0 := by
  classical
  simp [partialDensity]

end PartialDensity

section LowerUpperDensity

variable {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
variable (S A : Set α)

/-- Lower density is nonnegative when the order tends nontrivially to infinity. -/
theorem lowerDensity_nonneg [(atTop : Filter α).NeBot] : 0 ≤ S.lowerDensity A := by
  rw [lowerDensity]
  apply le_liminf_of_le
  · exact isCoboundedUnder_ge_of_le atTop fun b ↦ partialDensity_le_one S A b
  · exact Eventually.of_forall fun b ↦ partialDensity_nonneg S A b

/-- Upper density is at most `1` when the order tends nontrivially to infinity. -/
theorem upperDensity_le_one [(atTop : Filter α).NeBot] : S.upperDensity A ≤ 1 := by
  rw [upperDensity]
  apply limsup_le_of_le
  · exact isCoboundedUnder_le_of_le atTop fun b ↦ partialDensity_nonneg S A b
  · exact Eventually.of_forall fun b ↦ partialDensity_le_one S A b

/-- Lower density is at most upper density when the order tends nontrivially to infinity. -/
theorem lowerDensity_le_upperDensity [(atTop : Filter α).NeBot] :
    S.lowerDensity A ≤ S.upperDensity A := by
  rw [lowerDensity, upperDensity]
  apply liminf_le_limsup
  · exact isBoundedUnder_of_eventually_le <|
      Eventually.of_forall fun b ↦ partialDensity_le_one S A b
  · exact isBoundedUnder_of_eventually_ge <|
      Eventually.of_forall fun b ↦ partialDensity_nonneg S A b

/-- Upper density is nonnegative when the order tends nontrivially to infinity. -/
theorem upperDensity_nonneg [(atTop : Filter α).NeBot] : 0 ≤ S.upperDensity A :=
  (lowerDensity_nonneg S A).trans (lowerDensity_le_upperDensity S A)

/-- Lower density is at most `1` when the order tends nontrivially to infinity. -/
theorem lowerDensity_le_one [(atTop : Filter α).NeBot] : S.lowerDensity A ≤ 1 :=
  (lowerDensity_le_upperDensity S A).trans (upperDensity_le_one S A)

end LowerUpperDensity

section HasDensity

variable {α : Type*} [Preorder α] [LocallyFiniteOrderBot α]
variable {S A : Set α} {δ ε : ℝ}

/-- Asymptotic density is unique when the order tends nontrivially to infinity. -/
theorem HasDensity.unique [(atTop : Filter α).NeBot]
    (hδ : S.HasDensity δ A) (hε : S.HasDensity ε A) : δ = ε :=
  tendsto_nhds_unique hδ hε

/-- Exact density agrees with lower density. -/
theorem HasDensity.lowerDensity_eq [(atTop : Filter α).NeBot]
    (h : S.HasDensity δ A) : S.lowerDensity A = δ :=
  h.liminf_eq

/-- Exact density agrees with upper density. -/
theorem HasDensity.upperDensity_eq [(atTop : Filter α).NeBot]
    (h : S.HasDensity δ A) : S.upperDensity A = δ :=
  h.limsup_eq

/-- The empty set has density `0` relative to every reference set. -/
@[simp]
theorem hasDensity_empty (A : Set α := Set.univ) : HasDensity (∅ : Set α) 0 A := by
  refine tendsto_const_nhds.congr' ?_
  exact Eventually.of_forall fun b ↦ (partialDensity_empty A b).symm

open scoped Classical in
/-- The universal set has density `1` relative to `A` if the reference denominator is eventually
positive. -/
theorem hasDensity_univ (A : Set α)
    (hA : ∀ᶠ b in atTop, 0 < #{x ∈ Finset.Iio b | x ∈ A}) :
    HasDensity (Set.univ : Set α) 1 A := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hA] with b hb
  simp [partialDensity, Nat.ne_of_gt hb]

/-- A relative density is nonnegative. -/
theorem HasDensity.nonneg [(atTop : Filter α).NeBot] (h : S.HasDensity δ A) : 0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun b ↦ partialDensity_nonneg S A b

/-- A relative density is at most `1`. -/
theorem HasDensity.le_one [(atTop : Filter α).NeBot] (h : S.HasDensity δ A) : δ ≤ 1 :=
  le_of_tendsto h <| Eventually.of_forall fun b ↦ partialDensity_le_one S A b

end HasDensity

section NaturalDensity

variable {S A : Set ℕ} {δ ε : ℝ}

open scoped Classical in
/-- Relative partial density on the natural numbers is computed in `Finset.range n`. -/
theorem partialDensity_nat (S A : Set ℕ) (n : ℕ) :
    S.partialDensity A n =
      #{x ∈ Finset.range n | x ∈ S ∩ A} / #{x ∈ Finset.range n | x ∈ A} := by
  rw [partialDensity, Nat.Iio_eq_range]

open scoped Classical in
/-- The partial natural density of `S` is its proportion in `Finset.range n`. -/
theorem partialDensity_nat_univ (S : Set ℕ) (n : ℕ) :
    S.partialDensity (b := n) = #{x ∈ Finset.range n | x ∈ S} / n := by
  rw [partialDensity_nat]
  simp

open scoped Classical in
/-- Relative density on the natural numbers is convergence of relative proportions in
`Finset.range n`. -/
theorem hasDensity_nat_iff :
    S.HasDensity δ A ↔
      Tendsto
        (fun n : ℕ ↦
          (#{x ∈ Finset.range n | x ∈ S ∩ A} / #{x ∈ Finset.range n | x ∈ A} : ℝ))
        atTop (𝓝 δ) := by
  change Tendsto (fun n ↦ S.partialDensity A n) atTop (𝓝 δ) ↔ _
  simp_rw [partialDensity_nat]

open scoped Classical in
/-- A set has natural density `δ` exactly when its proportions in `Finset.range n` tend to `δ`. -/
theorem hasNaturalDensity_iff :
    S.HasNaturalDensity δ ↔
      Tendsto (fun n : ℕ ↦ (#{x ∈ Finset.range n | x ∈ S} / n : ℝ)) atTop (𝓝 δ) := by
  change Tendsto (fun n ↦ S.partialDensity (b := n)) atTop (𝓝 δ) ↔ _
  simp_rw [partialDensity_nat_univ]

/-- Natural density is unique. -/
theorem HasNaturalDensity.unique (hδ : S.HasNaturalDensity δ)
    (hε : S.HasNaturalDensity ε) : δ = ε :=
  HasDensity.unique hδ hε

/-- The empty set has natural density `0`. -/
@[simp]
theorem hasNaturalDensity_empty : HasNaturalDensity (∅ : Set ℕ) 0 :=
  hasDensity_empty

/-- The universal set has natural density `1`. -/
@[simp]
theorem hasNaturalDensity_univ : HasNaturalDensity (Set.univ : Set ℕ) 1 := by
  apply hasDensity_univ
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simpa using hn

open scoped Classical in
/-- A finite set of natural numbers has natural density `0`. -/
theorem Finite.hasNaturalDensity_zero (hS : S.Finite) : S.HasNaturalDensity 0 := by
  rw [hasNaturalDensity_iff]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_nonneg _)) ?_ (tendsto_const_div_atTop_nhds_zero_nat (#(hS.toFinset) : ℝ))
  exact Eventually.of_forall fun n ↦ by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    norm_cast
    apply Finset.card_le_card
    intro x hx
    exact hS.mem_toFinset.2 (Finset.mem_filter.1 hx).2

/-- A natural density is nonnegative. -/
theorem HasNaturalDensity.nonneg (h : S.HasNaturalDensity δ) : 0 ≤ δ :=
  HasDensity.nonneg h

/-- A natural density is at most `1`. -/
theorem HasNaturalDensity.le_one (h : S.HasNaturalDensity δ) : δ ≤ 1 :=
  HasDensity.le_one h

end NaturalDensity

end Set
