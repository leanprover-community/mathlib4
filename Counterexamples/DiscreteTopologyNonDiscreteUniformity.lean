/-
Copyright (c) 2024 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Discrete uniformities and discrete topology
Exactly as different metrics can induce equivalent topologies on a space, it is possible that
different uniform structures (a notion that generalises that of a metric structure) induce the same
topology on a space. In this file we are concerned in particular with the *discrete topology*,
formalised using the class `DiscreteTopology`, and the *discrete uniformity*, that is the bottom
element of the lattice of uniformities on a type (see `bot_uniformity`).

The theorem `discreteTopology_of_discrete_uniformity` shows that the topology induced by the
discrete uniformity is the discrete one, but it is well-known that the converse might not hold in
general, along the lines of the above discussion. We explicitly produce a metric and a uniform
structure on a space (on `ℕ`, actually) that are not discrete, yet induce the discrete topology.

To check that a certain uniformity is not discrete, recall that once a type `α` is endowed with a
uniformity, it is possible to speak about `Cauchy` filters on `a` and it is quite easy to see that
if the uniformity on `a` is the discrete one, a filter is Cauchy if and only if it coincides with
the principal filter `𝓟 {x}` (see `Filter.principal`) for some `x : α`. This is the
declaration `UniformSpace.DiscreteUnif.eq_const_of_cauchy` in Mathlib.

A special case of this result is the intuitive observation that a sequence `a : ℕ → ℕ` can be a
Cauchy sequence if and only if it is eventually constant: when claiming this equivalence, one is
implicitly endowing `ℕ` with the metric inherited from `ℝ`, that induces the discrete uniformity
on `ℕ`. Hence, the intuition suggesting that a Cauchy sequence, whose
terms are "closer and closer to each other", valued in `ℕ` must be eventually constant for
*topological* reasons, namely the fact that `ℕ` is a discrete topological space, is *wrong* in the
sense that the reason is intrinsically "metric". In particular, if a non-constant sequence (like
the identity `id : ℕ → ℕ` is Cauchy, then the uniformity is certainly *not discrete*.

## The counterexamples

We produce two counterexamples: in the first section `Metric` we construct a metric and in the
second section `SetPointUniformity` we construct a uniformity, explicitly as a filter on `ℕ × ℕ`.
They basically coincide, and the difference of the examples lies in their flavours.

### The metric

We begin  by defining a metric on `ℕ` (see `dist_def`) that
1. Induces the discrete topology, as proven in `TopIsDiscrete`;
2. Is not the discrete metric, in particular because the identity is a Cauchy sequence, as proven
in `idIsCauchy`

The definition is simply `dist m n = |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|`, and I am grateful to
Anatole Dedecker for his suggestion.

### The set-point theoretic uniformity
A uniformity on `ℕ` is a filter on `ℕ × ℕ` satisfying some properties: we define a sequence of
subsets `fundamentalEntourage n : (Set ℕ × ℕ)` (indexed by `n : ℕ`) and we observe it satisfies the
condition needed to be a basis of a filter: moreover, the filter generated by this basis satisfies
the condition for being a uniformity, and this is the uniformity we put on `ℕ`.

For each `n`, the set `fundamentalEntourage n : Set (ℕ × ℕ)` consists of the `n+1` points
`{(0,0),(1,1)...(n,n)}` on the diagonal; together with the half plane `{(x,y) | n ≤ x ∧ n ≤ y}`

That this collection can be used as a filter basis is proven in the definition `counterBasis` and
that the filter `counterBasis.filterBasis` is a uniformity is proven in the definition
`counterCoreUniformity`.

This induces the discrete topology, as proven in `TopIsDiscrete` and the `atTop` filter is Cauchy
(see `atTopIsCauchy`): that this specializes to the statement that the identity sequence
`id : ℕ → ℕ` is Cauchy is proven in `idIsCauchy`.

## Implementation details
Since most of the statements evolve around membership of explicit natural numbers (framed by some
inequality) to explicit subsets, many proofs are easily closed by `aesop` or `omega` or `linarith`.

### References
* [N. Bourbaki, *General Topology*, Chapter II][bourbaki1966]
-/

open Set Function Filter Metric

/- We remove the "usual" instances of (discrete) topological space and of (discrete) uniform space
from `ℕ`-/
attribute [-instance] instTopologicalSpaceNat instUniformSpaceNat

section Metric


noncomputable local instance : PseudoMetricSpace ℕ where
  dist := fun n m ↦ |2 ^ (- n : ℤ) - 2 ^ (- m : ℤ)|
  dist_self := by simp only [zpow_neg, zpow_natCast, sub_self, abs_zero, implies_true]
  dist_comm := fun _ _ ↦ abs_sub_comm ..
  dist_triangle := fun _ _ _ ↦ abs_sub_le ..

@[simp]
lemma dist_def {n m : ℕ} : dist n m = |2 ^ (-n : ℤ) - 2 ^ (-m : ℤ)| := rfl

lemma Int.eq_of_pow_sub_le {d : ℕ} {m n : ℤ} (hd1 : 1 < d)
    (h : |(d : ℝ) ^ (-m) - d ^ (-n)| < d ^ (-n - 1)) : m = n := by
  have hd0 : 0 < d := one_pos.trans hd1
  replace h : |(1 : ℝ) - d ^ (n - m)| < (d : ℝ)⁻¹ := by
    rw [← mul_lt_mul_iff_of_pos_left (a := (d : ℝ) ^ (-n)) (zpow_pos _ _),
      ← abs_of_nonneg (a := (d : ℝ) ^ (-n)) (le_of_lt <| zpow_pos _ _), ← abs_mul, mul_sub, mul_one,
      ← zpow_add₀ <| Nat.cast_ne_zero.mpr (ne_of_gt hd0), sub_eq_add_neg (b := m),
      neg_add_cancel_left, ← abs_neg, neg_sub,
      abs_of_nonneg (a := (d : ℝ) ^ (-n)) (le_of_lt <| zpow_pos _ _), ← zpow_neg_one,
      ← zpow_add₀ <| Nat.cast_ne_zero.mpr (ne_of_gt hd0), ← sub_eq_add_neg]
    exact h
    all_goals exact Nat.cast_pos'.mpr hd0
  by_cases H : (m : ℤ) ≤ n
  · obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr H)
    rw [ha, ← mul_lt_mul_iff_of_pos_left (a := (d : ℝ)) <| Nat.cast_pos'.mpr hd0,
      mul_inv_cancel₀ <| Nat.cast_ne_zero.mpr (ne_of_gt hd0),
      ← abs_of_nonneg (a := (d : ℝ)) <| Nat.cast_nonneg' d, ← abs_mul,
      show |(d : ℝ) * (1 - |(d : ℝ)| ^ (a : ℤ))| = |(d : ℤ) * (1 - |(d : ℤ)| ^ a)| by norm_cast,
      ← Int.cast_one (R := ℝ), Int.cast_lt, Int.abs_lt_one_iff, Int.mul_eq_zero,
      sub_eq_zero, eq_comm (a := 1), pow_eq_one_iff_cases] at h
    simp only [Nat.cast_eq_zero, ne_of_gt hd0, Nat.abs_cast, Nat.cast_eq_one, ne_of_gt hd1,
      Int.reduceNeg, reduceCtorEq, false_and, or_self, or_false, false_or] at h
    rwa [h, Nat.cast_zero, sub_eq_zero, eq_comm] at ha
  · have h1 : (d : ℝ) ^ (n - m) ≤ 1 - (d : ℝ)⁻¹ := calc
      (d : ℝ) ^ (n - m) ≤ (d : ℝ)⁻¹ := by
        rw [← zpow_neg_one]
        apply zpow_right_mono₀ <| Nat.one_le_cast.mpr hd0
        linarith
      _ ≤ 1 - (d : ℝ)⁻¹ := by
        rw [inv_eq_one_div, one_sub_div <| Nat.cast_ne_zero.mpr (ne_of_gt hd0),
          div_le_div_iff_of_pos_right <| Nat.cast_pos'.mpr hd0, le_sub_iff_add_le]
        norm_cast
    linarith [sub_lt_of_abs_sub_lt_right (a := (1 : ℝ)) (b := d ^ (n - m)) (c := d⁻¹) h]

lemma ball_eq_singleton {n : ℕ} : Metric.ball n ((2 : ℝ) ^ (-n - 1 : ℤ)) = {n} := by
  ext m
  constructor
  · zify [zpow_natCast, mem_ball, dist_def, mem_singleton_iff]
    apply Int.eq_of_pow_sub_le one_lt_two
  · intro H
    rw [H, mem_ball, dist_self]
    apply zpow_pos two_pos


theorem TopIsDiscrete : DiscreteTopology ℕ := by
  apply singletons_open_iff_discrete.mp
  intro
  simpa only [← ball_eq_singleton] using isOpen_ball

lemma idIsCauchy : CauchySeq (id : ℕ → ℕ) := by
  rw [Metric.cauchySeq_iff]
  refine fun ε ↦ Metric.cauchySeq_iff.mp
    (@cauchySeq_of_le_geometric_two ℝ _ 1 (fun n ↦ 2 ^(-n : ℤ)) fun n ↦ le_of_eq ?_) ε
  simp only [zpow_natCast, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg, one_div]
  rw [Real.dist_eq, zpow_add' <| Or.intro_left _ two_ne_zero]
  calc
    |2 ^ (- n : ℤ) - 2 ^ (-1 : ℤ) * 2 ^ (- n : ℤ)|
    _ = |(1 - (2 : ℝ)⁻¹) * 2 ^ (- n : ℤ)| := by rw [← one_sub_mul, zpow_neg_one]
    _ = |2⁻¹ * 2 ^ (-(n : ℤ))| := by congr; rw [inv_eq_one_div 2, sub_half 1]
    _ = 2⁻¹ / 2 ^ n := by rw [zpow_neg, abs_mul, abs_inv, abs_inv, inv_eq_one_div,
        Nat.abs_ofNat, one_div, zpow_natCast, abs_pow, ← div_eq_mul_inv, Nat.abs_ofNat]

end Metric

section SetPointUniformity

/- As the `instance PseudoMetricSpace ℕ` declared in the previous section was local, `ℕ` has no
topology at this point. We are going to define a non-discrete uniform structure (just using the
filter-based definition), that will endow it with a topology that we will eventually show to be
discrete. -/

/-- The fundamental entourages (index by `n : ℕ`) used to construct a basis of the uniformity: for
each `n`, the set `fundamentalEntourage n : Set (ℕ × ℕ)` consists of the `n+1` points
`{(0,0),(1,1)...(n,n)}` on the diagonal; together with the half plane `{(x,y) | n ≤ x ∧ n ≤ y}`-/
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
    · cases le_total n P.1 with
      | inl h_le => exact Or.inr ⟨h_le, h ▸ h_le⟩
      | inr h_le => exact Or.inl ⟨P.1, ⟨h_le, congrArg _ h⟩⟩

/-- The collection `fundamentalEntourage` satisfies the axioms to be a basis for a filter on
 `ℕ × ℕ` and gives rise to a term in the relevant type.-/
def counterBasis : FilterBasis (ℕ × ℕ) where
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
lemma mem_counterBasis_iff (S : Set (ℕ × ℕ)) :
    S ∈ counterBasis ↔ S ∈ range fundamentalEntourage := by
  dsimp [counterBasis]
  rfl

/-- The "crude" uniform structure, without topology, simply as a the filter generated by `Basis`
and satisfying the axioms for being a uniformity. We later extract the topology `counterTopology`
generated by it and bundle `counterCoreUniformity` and `counterTopology` in a uniform structure
on `ℕ`, proving in passing that `counterTopology = ⊥`-/
def counterCoreUniformity : UniformSpace.Core ℕ := by
  apply UniformSpace.Core.mkOfBasis counterBasis <;>
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
instance counterTopology : TopologicalSpace ℕ := counterCoreUniformity.toTopologicalSpace

/-- The uniform structure on `ℕ` bundling together the "crude" uniformity and the topology-/
instance counterUniformity : UniformSpace ℕ := UniformSpace.ofCore counterCoreUniformity

lemma HasBasis_counterUniformity :
    (uniformity ℕ).HasBasis (fun _ ↦ True) fundamentalEntourage := by
  show counterCoreUniformity.uniformity.HasBasis (fun _ ↦ True) fundamentalEntourage
  simp only [Filter.hasBasis_iff, exists_and_left, true_and]
  intro T
  refine ⟨fun ⟨s, ⟨⟨r, hr⟩, hs⟩⟩ ↦ ⟨r, subset_of_eq_of_subset hr hs⟩ , fun ⟨n, hn⟩ ↦ ?_⟩
  exact (@FilterBasis.mem_filter_iff _ counterBasis T).mpr ⟨fundamentalEntourage n, by simp, hn⟩

/-- A proof that the topology on `ℕ` induced by the "crude" uniformity `counterCoreUniformity`
(or by `counterUniformity` tout-court, since they are `defeq`) is discrete.-/
theorem TopIsDiscrete' : DiscreteTopology ℕ := by
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

/-- We find the same result about the identity map found in `idIsCauchy`, without using any metric
structure. -/
lemma idIsCauchy' : CauchySeq (id : ℕ → _) := ⟨map_neBot, cauchy_iff_le.mp atTopIsCauchy⟩

end SetPointUniformity
