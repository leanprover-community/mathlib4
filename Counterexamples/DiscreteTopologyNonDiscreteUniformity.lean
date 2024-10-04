/-
Copyright (c) 2024 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Order.Interval.Set.Basic

/-!
# Discrete uniformities and discrete topology
Exactly as different metrics can induce equivalent topologies on a space, it is possible that
different uniform structures (a notion that generalises that of a metric structure) induce the same
topology on a space. In this file we are concerned in particular with the *discrete topology*,
formalised using the class `DiscreteTopology`, and the *discrete uniformity*, that is the bottom
element of the lattice of uniformities on a type (see `bot_uniformity`).

The theorem `discreteTopology_of_discrete_uniformity` shows that the topology induced by the
discrete uniformity is the discrete one, but it is well-known that the converse might not hold in
general, along the lines of the above discussion.

Once a type `α` is endowed with a uniformity, it is possible to speak about `Cauchy` filters on `a`
and it is quite easy to see that if the uniformity on `a` is the discrete one, a filter is Cauchy if
and only if it the principal filter `𝓟 {x}` (see `Filter.principal`) and for some `x : α`. This is
the declaration `UniformSpace.DiscreteUnif.eq_const_of_cauchy` in Mathlib.

A special case of this result is the intuitive observation that a sequence `a : ℕ → ℕ` can be a
Cauchy sequence if and only if it is eventually constant: when claiming this equivalence, one is
implicitely endowing `ℕ` with the metric inherited from `ℝ`, that induces the discrete uniformity
on `ℕ`: on the other hand, the geometric intuition might suggest that a Cauchy sequence, whose
terms are "closer and closer to each other", valued in `ℕ` must be eventually constant for
*topological* reasons, namely the fact that `ℕ` is a discrete topological space.

## The question and the counterexample
It is natural to wonder whether the assumption of `UniformSpace.DiscreteUnif.eq_const_of_cauchy`
that the uniformity is discrete can be relaxed to assume that the *topology* is discrete. In other
terms, is it true that every Cauchy sequence in a uniform space whose topology is discrete is
eventually constant? In the language of filters: is it true that every Cauchy filter `ℱ` in a
uniform space `α` whose induced topology `UniformSpace.toTopologicalSpace` is discrete, is of the
form `ℱ = 𝓟 {x}` for some `x : α`?

The goal of this file is to show that the answer is "no", by providing a counterexample. We
construct a uniform structure on `ℕ`, showing that it induces the discrete topology on `ℕ` but
such that the filter `Filter.atTop` (that can be of the form `𝓟 {x}` only when `x` is a top
element, which is not the case if `α = ℕ`) is Cauchy. In particular, the identity sequence
`fun x ↦ x : ℕ → ℕ` is a Cauchy sequence valued in the discrete topological space `ℕ`.

## The construction of the uniformity
A uniformity on `ℕ` is a filter on `ℕ × ℕ` satisfying some properties: we define a sequence of
subsets `fundamentalEntourage n : (Set ℕ × ℕ)` (indexed by `n : ℕ`) and we observe it satisfies the
condition needed to be a basis of a filter: moreover, the filter generated by this basis satisfies
the condition for being a uniformity, and this is the uniformity we put on `ℕ`.

For each `n`, the set `fundamentalEntourage n : Set (ℕ × ℕ)` consists of the `n+1` points
`{(0,0),(1,1)...(n,n)}` on the diagonal; together with the half plane `{(x,y) | n ≤ x  ∧ n ≤ y}`

That this collection can be used as a filter basis is proven in the definition `Basis` and that
the filter `Basis.filterBasis` is a uniformity is proven in the definition `counterCoreUniformity`.

This induces the discrete topology, as proven in `TopIsDiscrete` and the `atTop` filter is Cauchy
(see `atTopIsCauchy`): that this specializes to the statement that the identity sequence
`id : ℕ → ℕ` is Cauchy is proven in `idIsCauchy`.

## Implementation detail
Since most of the statements evolve around membership of explicit natural numbers (framed by some
inequality) to explicit subsets, many proofs are easily closed by `aesop` or `omega`.

### References
* [N. Bourbaki, *General Topology*, Chapter II][bourbaki1966]
-/


open Set Function Filter

/- We remove the "usual" instances of (discrete) topological space and of (discrete) uniform space
from `ℕ`-/
attribute [-instance] instTopologicalSpaceNat instUniformSpaceNat


/-- The fundamental entourages (index by `n : ℕ`) used to construct a basis of the uniformity: for
each `n`, the set `fundamentalEntourage n : Set (ℕ × ℕ)` consists of the `n+1` points
`{(0,0),(1,1)...(n,n)}` on the diagonal; together with the half plane `{(x,y) | n ≤ x  ∧ n ≤ y}`-/
def fundamentalEntourage (n : ℕ) : Set (ℕ × ℕ) :=
  (⋃ i : Icc 0 n, {((i : ℕ), (i : ℕ))}) ∪ Set.Ici (n , n)

@[simp]
lemma fundamentalEntourage_ext (t : ℕ) (T : Set (ℕ × ℕ)) : fundamentalEntourage t = T ↔
    T = (⋃ i : Icc 0 t, {((i : ℕ), (i : ℕ))}) ∪ Set.Ici (t , t) := by
  simpa only [fundamentalEntourage] using eq_comm

lemma mem_range_fundamentalEntourage (S : Set (ℕ × ℕ)) :
  S ∈ (range fundamentalEntourage) ↔ ∃ n, fundamentalEntourage n = S := by
  simp only [Set.mem_range, Eq.symm]

lemma mem_fundamentalEntourage (n : ℕ) (P : ℕ × ℕ) : P ∈ fundamentalEntourage n ↔
  (n ≤ P.1 ∧ n ≤ P.2) ∨ (P.1 = P.2) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [fundamentalEntourage, iUnion_singleton_eq_range, mem_union, mem_range,
      Subtype.exists, mem_Icc, zero_le, true_and, exists_prop', nonempty_prop, mem_Ici] at h
    rcases h with h | h
    · apply Or.inr
      rw [((h.choose_spec).2).symm]
    · exact Or.inl h
  · simp only [iUnion_singleton_eq_range, mem_union, mem_range, Subtype.exists, mem_Icc, zero_le,
      true_and, exists_prop', nonempty_prop, mem_Ici, fundamentalEntourage]
    rcases h with h | h
    · exact Or.inr h
    · by_cases h_le : n ≤ P.1
      · exact Or.inr ⟨h_le, h ▸ h_le⟩
      · refine Or.inl ⟨P.1, ⟨le_of_lt <| not_le.mp h_le, congrArg _ h⟩⟩

/-- The collection `fundamentalEntourage` satisfies the axioms to be a basis for a filter on
 `ℕ × ℕ` and gives rise to a term in the relevant type.-/
def Basis : FilterBasis (ℕ × ℕ) where
  sets := range fundamentalEntourage
  nonempty := range_nonempty _
  inter_sets := by
    intro S T hS hT
    obtain ⟨s, hs⟩ := hS
    obtain ⟨t, ht⟩ := hT
    simp only [mem_range, subset_inter_iff, exists_exists_eq_and, fundamentalEntourage]
    use max t s
    refine ⟨fun ⟨P1, P2⟩ hP ↦ ?_, fun ⟨P1, P2⟩ hP ↦ ?_⟩ <;>
    cases' hP with h h <;>
    simp only [iUnion_singleton_eq_range, mem_range, Prod.mk.injEq, Subtype.exists, mem_Icc,
      zero_le, le_max_iff, true_and, exists_and_left, exists_prop', nonempty_prop,
      exists_eq_left] at h
    · simpa only [← hs, mem_fundamentalEntourage] using Or.inr h.2
    · simpa only [← hs, mem_fundamentalEntourage] using Or.inl
        ⟨le_trans (by omega) h.1, le_trans (by omega) h.2⟩
    · simpa only [← ht, mem_fundamentalEntourage] using Or.inr h.2
    · simp only [mem_Ici, Prod.mk_le_mk] at h
      simpa only [← ht, mem_fundamentalEntourage] using Or.inl ⟨le_trans
         (by omega) h.1, le_trans (by omega) h.2⟩

@[simp]
lemma mem_Basis_iff (S : Set (ℕ × ℕ)) : S ∈ Basis ↔ S ∈ range fundamentalEntourage := by
  dsimp [Basis]
  rfl

/-- The "crude" uniform structure, without topology, simply as a the filter generated by `Basis`
and satisfying the axioms for being a uniformity. We later extract the topology `counterTopology`
generated by it and bundle `counterCoreUniformity` and `counterTopology` in a uniform strucutre
on `ℕ`, proving in passing that `counterTopology = ⊥`-/
def counterCoreUniformity : UniformSpace.Core ℕ := by
  apply UniformSpace.Core.mkOfBasis Basis <;>
  intro S hS
  · obtain ⟨n, hn⟩ := hS
    simp only [fundamentalEntourage_ext, iUnion_singleton_eq_range] at hn
    simp only [hn, mem_union, mem_range, Prod.mk.injEq, and_self, Subtype.exists, mem_Icc, zero_le,
      true_and, exists_prop', nonempty_prop, exists_eq_right, mem_Ici, Prod.mk_le_mk]
    omega
  · refine ⟨S, hS, ?_⟩
    obtain ⟨n, hn⟩ := hS
    simp only [fundamentalEntourage_ext, iUnion_singleton_eq_range] at hn
    simp only [hn, preimage_union, union_subset_iff]
    constructor
    · apply subset_union_of_subset_left (subset_of_eq _)
      aesop
    · apply subset_union_of_subset_right (subset_of_eq _)
      aesop
  · refine ⟨S, hS, ?_⟩
    obtain ⟨n, hn⟩ := hS
    simp only [fundamentalEntourage_ext, iUnion_singleton_eq_range] at hn
    simp only [hn, mem_union, mem_range, Prod.mk.injEq, Subtype.exists, mem_Icc, zero_le, true_and,
      exists_and_left, exists_prop', nonempty_prop, exists_eq_left, mem_Ici, Prod.mk_le_mk]
    rintro ⟨P1, P2⟩ ⟨m, h1, h2⟩
    simp only [mem_union, mem_range, Prod.mk.injEq, Subtype.exists, mem_Icc, zero_le, true_and,
      exists_and_left, exists_prop', nonempty_prop, exists_eq_left, mem_Ici, Prod.mk_le_mk] at h1 h2
    aesop

/--The topology on `ℕ` induced by the "crude" uniformity-/
instance counterTopology: TopologicalSpace ℕ := counterCoreUniformity.toTopologicalSpace

/-- The uniform structure on `ℕ` bundling together the "crude" uniformity and the topology-/
instance counterUniformity: UniformSpace ℕ := UniformSpace.ofCore counterCoreUniformity

lemma HasBasis_counterUniformity :
    (uniformity ℕ).HasBasis (fun _ ↦ True) fundamentalEntourage := by
  show counterCoreUniformity.uniformity.HasBasis (fun _ ↦ True) fundamentalEntourage
  simp only [Filter.hasBasis_iff, exists_and_left, true_and]
  intro T
  refine ⟨fun ⟨s, ⟨⟨r, hr⟩, hs⟩⟩ ↦ ⟨r, subset_of_eq_of_subset hr hs⟩ , fun ⟨n, hn⟩ ↦ ?_⟩
  exact (@FilterBasis.mem_filter_iff _ Basis T).mpr ⟨fundamentalEntourage n, by simp, hn⟩

/- A proof that the topology on `ℕ` induced by the "crude" uniformity `counterCoreUniformity` (or by
`counterUniformity` tout-court, since they are `defeq`) is discrete. -/
theorem TopIsDiscrete : DiscreteTopology ℕ := by
  rw [discreteTopology_iff_nhds]
  intro n
  rw [nhds_eq_comap_uniformity']
  apply Filter.ext
  intro S
  simp only [Filter.mem_comap, Filter.mem_pure]
  have := @Filter.HasBasis.mem_uniformity_iff _ _ _ _ _ HasBasis_counterUniformity
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp_rw [this] at h
    obtain ⟨T, ⟨⟨i, ⟨-, h1⟩⟩, h2⟩⟩ := h
    apply h2 (h1 _ _ _)
    rw [mem_fundamentalEntourage]
    aesop
  · refine ⟨fundamentalEntourage (n + 1), ?_, ?_⟩
    · show fundamentalEntourage (n + 1) ∈ counterCoreUniformity.uniformity
      exact @Filter.HasBasis.mem_of_mem (ℕ × ℕ) ℕ counterCoreUniformity.uniformity (fun _ ↦ True)
        fundamentalEntourage (n + 1) HasBasis_counterUniformity trivial
    · simp only [preimage_subset_iff, mem_fundamentalEntourage, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, and_false, false_or]
      exact fun _ a ↦ mem_of_eq_of_mem a h

/- With respect to the above uniformity, the `atTop` filter is Cauchy; in particular, it is not of
the form `𝓟 {x}` for any `x`, although the topology is discrete. This implies in passing that this
uniformity is not discrete-/
lemma atTopIsCauchy : Cauchy (atTop : Filter ℕ) := by
  rw [HasBasis_counterUniformity.cauchy_iff]
  refine ⟨atTop_neBot, fun i _ ↦ ?_⟩
  simp_rw [mem_fundamentalEntourage, mem_atTop_sets, ge_iff_le]
  exact ⟨Ici i, ⟨⟨i, fun _ hb ↦ hb⟩, fun _ hx _ hy ↦ Or.inl ⟨hx, hy⟩⟩⟩

lemma idIsCauchy : CauchySeq (id : ℕ → _) := ⟨map_neBot, cauchy_iff_le.mp atTopIsCauchy⟩
