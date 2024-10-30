/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Algebra.Monoid

/-! # Approximate units

An *approximate unit* is a filter `l` such that multiplication on the left (or right) by `m : α`
tends to `𝓝 m` along the filter, and additionally `l ≠ ⊥` and `Disjoint l (cobounded α)`.


Examples of approximate units include:

- The trivial approximate unit `pure 1` in a normed ring.
- `𝓝 1` or `𝓝[≠] 1` in a normed ring (note that the latter is disjoint from `pure 1`).
- In a C⋆-algebra, the collection of sections `fun a ↦ {x | a ≤ x} ∩ ball 0 1`, where `a`
  ranges over the positive elements of norm strictly less than 1, is a filter basis for an
  approximate unit.

In many cases of interest, an approximate unit is specified by a filter basis with certain
properties, and the filter itself is of less interest. For instance, in the case of non-unital
C⋆-algebras, the canonical approximate unit is the one derived from the net of nonnegative elements
contained in the unit ball. This set is directed under the natural star order:
`x ≤ y ↔ ∃ s, y = x + star s * s`. In order to reduce the type class burden, we only require a
bornology on the underlying type.

One reason to help explain why the filter is of less interest than the basis is that there may be
*many* approximate units, and they may even be disjoint! Indeed, in a topological unital magma,
the approximate units are precisely the proper filters contained in `𝓝 1`.
-/

open Filter Topology Bornology

/-- An *approximate unit* is a proper bounded filter (i.e., `≠ ⊥` and disjoint from `cobounded α`)
such that multiplication on the left (and separately on the right) by `m : α` tends to `𝓝 m` along
the filter. -/
structure IsApproximateUnit {α : Type*} [TopologicalSpace α] [Mul α] [Bornology α]
    (l : Filter α) : Prop where
  /-- Multiplication on the left by `m` tends to `𝓝 m` along the filter. -/
  tendsto_mul_left m : Tendsto (m * ·) l (𝓝 m)
  /-- Multiplication on the right by `m` tends to `𝓝 m` along the filter. -/
  tendsto_mul_right m : Tendsto (· * m) l (𝓝 m)
  /-- The filter is bounded. -/
  disjoint_cobounded : Disjoint l (cobounded α)
  /-- The filter is not `⊥`. -/
  protected [neBot : NeBot l]

namespace IsApproximateUnit

/-- A unital magma with a topology and bornology has the trivial approximate unit `pure 1`. -/
lemma pure_one (α : Type*) [TopologicalSpace α] [MulOneClass α] [Bornology α] :
    IsApproximateUnit (pure (1 : α))  where
  tendsto_mul_left m := by simpa using tendsto_pure_nhds (m * ·) (1 : α)
  tendsto_mul_right m := by simpa using tendsto_pure_nhds (· * m) (1 : α)
  disjoint_cobounded := Filter.hasBasis_pure 1 |>.disjoint_cobounded_iff.mpr <| by simp

set_option linter.unusedVariables false in
/-- If `l` is an approximate unit and `⊥ < l' ≤ l`, then `l'` is also an approximate
unit. -/
lemma of_le {α : Type*} [TopologicalSpace α] [MulOneClass α] [Bornology α]
    {l l' : Filter α} (hl : IsApproximateUnit l) (hle : l' ≤ l) [hl' : l'.NeBot] :
    IsApproximateUnit l' where
  tendsto_mul_left m := hl.tendsto_mul_left m |>.mono_left hle
  tendsto_mul_right m := hl.tendsto_mul_right m |>.mono_left hle
  disjoint_cobounded := hl.disjoint_cobounded.mono_left hle

/-- In a metric space which is a topological unital magma, `𝓝 1` is an approximate unit. -/
lemma nhds_one (α : Type*) [PseudoMetricSpace α] [MulOneClass α]
    [ContinuousMul α] : IsApproximateUnit (𝓝 (1 : α)) where
  tendsto_mul_left m := by simpa using tendsto_id (x := 𝓝 1) |>.const_mul m
  tendsto_mul_right m := by simpa using tendsto_id (x := 𝓝 1) |>.mul_const m
  disjoint_cobounded := Metric.disjoint_nhds_cobounded (1 : α)

/-- In a metric space which is a topological unital magma, `𝓝 1` is the largest approximate unit. -/
lemma iff_neBot_and_le_nhds_one {α : Type*} [PseudoMetricSpace α] [MulOneClass α]
    [ContinuousMul α] {l : Filter α} :
    IsApproximateUnit l ↔ l.NeBot ∧ l ≤ 𝓝 1 :=
  ⟨fun hl ↦ ⟨hl.neBot, by simpa using hl.tendsto_mul_left 1⟩,
    And.elim fun _ hl ↦ IsApproximateUnit.nhds_one α |>.of_le hl⟩

@[to_additive]
lemma mulLeftRightTendsto.le_iff {l : Filter α} :
    l ≤ mulLeftRightTendsto ↔ ∀ m, Tendsto (· * m) l (𝓝 m) ∧ Tendsto (m * ·) l (𝓝 m) :=
  ⟨fun h m ↦ ⟨(tendsto_mul_left m).mono_left h, (tendsto_mul_right m).mono_left h⟩,
    fun h ↦ le_sSup h⟩

end Filter

variable [Bornology α]

/-- An *approximate unit* is a filter smaller than `mulLeftRightTendsto` along with a basis
consisting of sets contained in a given bounded set. The former condition is equivalent to the
condition that for all `m`, multiplication on the left (or right) tends to `m` along the filter.

Note: this extends `Filter` and `Filter.HasBasis` rather than taking the filter as an argument.
This is because, in many cases, the only interesting property of the filter is that it is smaller
than `mulLeftRightTendsto` and we may only be interested in the filter basis itself. -/
structure ApproximateUnit (p : ι → Prop) (s : ι → Set α)
    extends Filter α, toFilter.HasBasis p s where
  /-- The filter generated by the basis is smaller than `Filter.mulLeftRightTendsto`. -/
  filter_le : toFilter ≤ mulLeftRightTendsto
  /-- All elements of the basis are bounded. -/
  bounded : ∃ t, IsBounded t ∧ ∀ i, p i → s i ⊆ t
  /-- The filter generated by the basis is not `⊥`. -/
  protected [neBot : NeBot toFilter]

/-- Create an approximate unit from a filter basis satisfying the necessary properties. -/
@[simps toFilter toHasBasis]
def Filter.IsBasis.approximateUnit {p : ι → Prop} {s : ι → Set α} (b : IsBasis p s)
    (h_le : b.filter ≤ mulLeftRightTendsto)
    (h_bdd : ∃ t, Bornology.IsBounded t ∧ ∀ i, p i → s i ⊆ t)
    (h_neBot : ∀ i, p i → (s i).Nonempty) : ApproximateUnit p s where
  toFilter := b.filter
  toHasBasis := b.hasBasis
  filter_le := h_le
  bounded := h_bdd
  neBot := by rwa [b.hasBasis.neBot_iff]

variable {p : ι → Prop} {s : ι → Set α}

lemma tendsto_mul_left (au : ApproximateUnit p s) (m : α) :
    Tendsto (· * m) au.toFilter (𝓝 m) :=
  mulLeftRightTendsto.le_iff.mp au.filter_le m |>.1

lemma tendsto_mul_right (au : ApproximateUnit p s) (m : α) :
    Tendsto (m * ·) au.toFilter (𝓝 m) :=
  mulLeftRightTendsto.le_iff.mp au.filter_le m |>.2

end Def

/-- A unital magma with a topology and bornology has the trivial approximate unit `𝓟 {1}` with
basis `{1}`. -/
@[simps toFilter toHasBasis]
def ApproximateUnit.ofUnit (α : Type*) [TopologicalSpace α] [MulOneClass α] [Bornology α] :
    ApproximateUnit (fun _ => True) (fun _ : Unit => {(1 : α)}) where
  toFilter := 𝓟 {1}
  toHasBasis := Filter.hasBasis_principal {1}
  filter_le := by simpa [mulLeftRightTendsto.le_iff, tendsto_pure_left]
    using fun _ _ ↦ mem_of_mem_nhds
  bounded := ⟨{1}, by simp⟩
  neBot := principal_neBot_iff.2 <| Set.singleton_nonempty 1

section DirectedOn

/-- If `s : Set α` is a nonempty directed set, then the collection of sections `{x | · ≤ x} ∩ s`
contained in `s` forms a basis for a filter on `α`. -/
lemma DirectedOn.filterIsBasis {α : Type*} [Preorder α] {s : Set α}
    (h : DirectedOn (· ≤ ·) s) (hs : s.Nonempty) :
    Filter.IsBasis (· ∈ s) ({x | · ≤ x} ∩ s) where
  nonempty := hs
  inter {x y} hx hy := by
    obtain ⟨z, hz, hxz, hyz⟩ := h x hx y hy
    refine ⟨z, hz, fun w hw ↦ ?_⟩
    have : x ≤ w ∧ y ≤ w := ⟨hxz.trans hw.1, hyz.trans hw.1⟩
    aesop

end DirectedOn
